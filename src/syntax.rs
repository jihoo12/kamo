use crate::arena::{Arena, key};
use crate::{Error, Result};
use std::collections::HashMap;
key!(TermId);

#[derive(Clone, Copy, Debug)]
pub(crate) enum D {
    Zero,
    One,
    Bound(usize),
}
#[derive(Clone, Debug)]
pub(crate) enum F {
    Top,
    Bot,
    Eq(D, D),
    And(Box<F>, Box<F>),
    Or(Box<F>, Box<F>),
}
#[derive(Clone, Debug)]
pub(crate) enum Term {
    Var(usize),
    Global(usize),
    U(u32),
    Pi(TermId, TermId),
    Sigma(TermId, TermId),
    Lam(TermId),
    App(TermId, TermId),
    Pair(TermId, TermId),
    Fst(TermId),
    Snd(TermId),
    Bool,
    True,
    False,
    If(TermId, TermId, TermId, TermId),
    Nat,
    Zero,
    Suc(TermId),
    NatElim(TermId, TermId, TermId, TermId),
    Ann(TermId, TermId),
    Path(TermId, TermId, TermId),
    PLam(TermId),
    PApp(TermId, D),
    Com {
        family: TermId,
        from: D,
        to: D,
        cap: TermId,
        tubes: Vec<(F, TermId)>,
    },
    System(TermId, Vec<(F, TermId)>),
    Glue(TermId, Vec<(F, TermId, TermId)>),
    GlueIntro(TermId, TermId, Vec<(F, TermId)>),
    Unglue(TermId, TermId),
}
#[derive(Clone, Debug)]
pub(crate) struct Node {
    pub term: Term,
    pub offset: usize,
}
#[derive(Clone, Debug)]
pub(crate) struct Decl {
    pub name: String,
    pub ty: TermId,
    pub body: TermId,
}
#[derive(Default, Debug)]
pub(crate) struct Program {
    pub terms: Arena<TermId, Node>,
    pub decls: Vec<Decl>,
}
#[derive(Debug)]
struct S {
    kind: Kind,
    offset: usize,
}
#[derive(Debug)]
enum Kind {
    Atom(String),
    List(Vec<S>),
}
impl S {
    fn atom(&self) -> Result<&str> {
        if let Kind::Atom(a) = &self.kind {
            Ok(a)
        } else {
            Err(Error::at(self.offset, "expected a name"))
        }
    }
    fn list(&self) -> Result<&[S]> {
        if let Kind::List(a) = &self.kind {
            Ok(a)
        } else {
            Err(Error::at(self.offset, "expected a list"))
        }
    }
}
fn sexps(source: &str) -> Result<Vec<S>> {
    fn ws(s: &[u8], i: &mut usize) {
        loop {
            while *i < s.len() && s[*i].is_ascii_whitespace() {
                *i += 1;
            }
            if s.get(*i) == Some(&b';') {
                while *i < s.len() && s[*i] != b'\n' {
                    *i += 1;
                }
            } else {
                break;
            }
        }
    }
    fn one(source: &str, i: &mut usize, depth: usize) -> Result<S> {
        if depth > 512 {
            return Err(Error::at(*i, "syntax nesting exceeds 512"));
        }
        let s = source.as_bytes();
        ws(s, i);
        let offset = *i;
        match s.get(*i) {
            Some(b'(') => {
                *i += 1;
                let mut xs = vec![];
                loop {
                    ws(s, i);
                    match s.get(*i) {
                        Some(b')') => {
                            *i += 1;
                            break;
                        }
                        None => return Err(Error::at(offset, "unclosed list")),
                        _ => xs.push(one(source, i, depth + 1)?),
                    }
                }
                Ok(S {
                    kind: Kind::List(xs),
                    offset,
                })
            }
            Some(b')') => Err(Error::at(offset, "unexpected ')'")),
            Some(_) => {
                while *i < s.len() && !s[*i].is_ascii_whitespace() && !b"();".contains(&s[*i]) {
                    *i += 1;
                }
                Ok(S {
                    kind: Kind::Atom(source[offset..*i].into()),
                    offset,
                })
            }
            None => Err(Error::at(offset, "expected expression")),
        }
    }
    let mut i = 0;
    let mut out = vec![];
    loop {
        ws(source.as_bytes(), &mut i);
        if i == source.len() {
            return Ok(out);
        }
        out.push(one(source, &mut i, 0)?);
    }
}
struct Parser {
    program: Program,
    globals: HashMap<String, usize>,
    terms: Vec<String>,
    dims: Vec<String>,
}
impl Parser {
    fn dim(&self, s: &S) -> Result<D> {
        match s.atom()? {
            "0" => Ok(D::Zero),
            "1" => Ok(D::One),
            n => self
                .dims
                .iter()
                .rev()
                .position(|x| x == n)
                .map(D::Bound)
                .ok_or_else(|| Error::at(s.offset, format!("unknown interval variable '{n}'"))),
        }
    }
    fn face(&self, s: &S) -> Result<F> {
        if let Kind::Atom(n) = &s.kind {
            return match n.as_str() {
                "top" => Ok(F::Top),
                "bottom" => Ok(F::Bot),
                _ => Err(Error::at(s.offset, "expected face formula")),
            };
        }
        let xs = s.list()?;
        if xs.len() != 3 {
            return Err(Error::at(s.offset, "face operator requires two arguments"));
        }
        match xs[0].atom()? {
            "=" => Ok(F::Eq(self.dim(&xs[1])?, self.dim(&xs[2])?)),
            "and" => Ok(F::And(
                Box::new(self.face(&xs[1])?),
                Box::new(self.face(&xs[2])?),
            )),
            "or" => Ok(F::Or(
                Box::new(self.face(&xs[1])?),
                Box::new(self.face(&xs[2])?),
            )),
            _ => Err(Error::at(s.offset, "unknown face operator")),
        }
    }
    fn bind(&mut self, name: &S, body: &S, dim: bool) -> Result<TermId> {
        let n = name.atom()?.to_owned();
        if dim {
            self.dims.push(n);
        } else {
            self.terms.push(n);
        }
        let b = self.term(body);
        if dim {
            self.dims.pop();
        } else {
            self.terms.pop();
        }
        b
    }
    fn term(&mut self, s: &S) -> Result<TermId> {
        let t = match &s.kind {
            Kind::Atom(n) => match n.as_str() {
                "Bool" => Term::Bool,
                "true" => Term::True,
                "false" => Term::False,
                "Nat" => Term::Nat,
                "zero" => Term::Zero,
                _ => {
                    if let Some(i) = self.terms.iter().rev().position(|x| x == n) {
                        Term::Var(i)
                    } else if let Some(i) = self.globals.get(n) {
                        Term::Global(*i)
                    } else {
                        return Err(Error::at(s.offset, format!("unknown name '{n}'")));
                    }
                }
            },
            Kind::List(xs) => {
                if xs.is_empty() {
                    return Err(Error::at(s.offset, "empty expression"));
                }
                let op = xs[0].atom()?;
                let arity = |n: usize| {
                    if xs.len() == n + 1 {
                        Ok(())
                    } else {
                        Err(Error::at(s.offset, format!("'{op}' expects {n} arguments")))
                    }
                };
                match op {
                    "U" => {
                        arity(1)?;
                        Term::U(xs[1].atom()?.parse().map_err(|_| {
                            Error::at(xs[1].offset, "expected a universe level (u32)")
                        })?)
                    }
                    "Pi" | "Sigma" => {
                        arity(3)?;
                        let a = self.term(&xs[2])?;
                        let b = self.bind(&xs[1], &xs[3], false)?;
                        if op == "Pi" {
                            Term::Pi(a, b)
                        } else {
                            Term::Sigma(a, b)
                        }
                    }
                    "lam" => {
                        arity(2)?;
                        Term::Lam(self.bind(&xs[1], &xs[2], false)?)
                    }
                    "app" | "pair" | "ann" => {
                        arity(2)?;
                        let a = self.term(&xs[1])?;
                        let b = self.term(&xs[2])?;
                        match op {
                            "app" => Term::App(a, b),
                            "pair" => Term::Pair(a, b),
                            _ => Term::Ann(a, b),
                        }
                    }
                    "fst" | "snd" | "suc" => {
                        arity(1)?;
                        let a = self.term(&xs[1])?;
                        match op {
                            "fst" => Term::Fst(a),
                            "snd" => Term::Snd(a),
                            _ => Term::Suc(a),
                        }
                    }
                    "bool-elim" | "nat-elim" => {
                        arity(4)?;
                        let p = self.term(&xs[1])?;
                        let a = self.term(&xs[2])?;
                        let b = self.term(&xs[3])?;
                        let c = self.term(&xs[4])?;
                        if op == "bool-elim" {
                            Term::If(p, a, b, c)
                        } else {
                            Term::NatElim(p, a, b, c)
                        }
                    }
                    "Path" => {
                        arity(4)?;
                        let a = self.bind(&xs[1], &xs[2], true)?;
                        let l = self.term(&xs[3])?;
                        let r = self.term(&xs[4])?;
                        Term::Path(a, l, r)
                    }
                    "path" => {
                        arity(2)?;
                        Term::PLam(self.bind(&xs[1], &xs[2], true)?)
                    }
                    "at" => {
                        arity(2)?;
                        Term::PApp(self.term(&xs[1])?, self.dim(&xs[2])?)
                    }
                    "coe" | "com" => {
                        arity(if op == "coe" { 5 } else { 6 })?;
                        let from = self.dim(&xs[3])?;
                        let to = self.dim(&xs[4])?;
                        let cap = self.term(&xs[5])?;
                        let family = self.bind(&xs[1], &xs[2], true)?;
                        let mut tubes = vec![];
                        if op == "com" {
                            for branch in xs[6].list()? {
                                let b = branch.list()?;
                                if b.len() != 2 {
                                    return Err(Error::at(branch.offset, "expected (face body)"));
                                }
                                let f = self.face(&b[0])?;
                                let t = self.bind(&xs[1], &b[1], true)?;
                                tubes.push((f, t));
                            }
                        }
                        Term::Com {
                            family,
                            from,
                            to,
                            cap,
                            tubes,
                        }
                    }
                    "system" => {
                        arity(2)?;
                        let a = self.term(&xs[1])?;
                        let mut bs = vec![];
                        for b in xs[2].list()? {
                            let b = b.list()?;
                            if b.len() != 2 {
                                return Err(Error::at(s.offset, "expected (face body)"));
                            }
                            bs.push((self.face(&b[0])?, self.term(&b[1])?));
                        }
                        Term::System(a, bs)
                    }
                    "Glue" => {
                        arity(2)?;
                        let a = self.term(&xs[1])?;
                        let mut bs = vec![];
                        for branch in xs[2].list()? {
                            let b = branch.list()?;
                            if b.len() != 3 {
                                return Err(Error::at(
                                    branch.offset,
                                    "expected (face type equivalence)",
                                ));
                            }
                            bs.push((self.face(&b[0])?, self.term(&b[1])?, self.term(&b[2])?));
                        }
                        Term::Glue(a, bs)
                    }
                    "glue" => {
                        arity(3)?;
                        let g = self.term(&xs[1])?;
                        let a = self.term(&xs[2])?;
                        let mut bs = vec![];
                        for branch in xs[3].list()? {
                            let b = branch.list()?;
                            if b.len() != 2 {
                                return Err(Error::at(branch.offset, "expected (face term)"));
                            }
                            bs.push((self.face(&b[0])?, self.term(&b[1])?));
                        }
                        Term::GlueIntro(g, a, bs)
                    }
                    "unglue" => {
                        arity(2)?;
                        Term::Unglue(self.term(&xs[1])?, self.term(&xs[2])?)
                    }
                    _ => return Err(Error::at(s.offset, format!("unknown form '{op}'"))),
                }
            }
        };
        Ok(self.program.terms.alloc(Node {
            term: t,
            offset: s.offset,
        }))
    }
}
pub(crate) fn parse(source: &str) -> Result<Program> {
    let mut p = Parser {
        program: Program::default(),
        globals: HashMap::new(),
        terms: vec![],
        dims: vec![],
    };
    for s in sexps(source)? {
        let xs = s.list()?;
        if xs.len() != 4 || xs[0].atom()? != "def" {
            return Err(Error::at(s.offset, "expected (def name type body)"));
        }
        let name = xs[1].atom()?.to_owned();
        if p.globals.contains_key(&name)
            || ["Bool", "Nat", "true", "false", "zero"].contains(&name.as_str())
        {
            return Err(Error::at(
                xs[1].offset,
                "duplicate or reserved declaration name",
            ));
        }
        let ty = p.term(&xs[2])?;
        let body = p.term(&xs[3])?;
        p.globals.insert(name.clone(), p.program.decls.len());
        p.program.decls.push(Decl { name, ty, body });
    }
    Ok(p.program)
}
