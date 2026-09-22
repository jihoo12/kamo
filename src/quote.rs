//! Iterative, type-directed quotation into one bounded output buffer.
use crate::eval::{Engine, Val, ValId};
use crate::face::{Dim, FaceId};
use crate::{Error, Result};

#[derive(Default)]
struct Names {
    terms: Vec<u32>,
    dims: Vec<u32>,
    dim_levels: Vec<u32>,
}
impl Names {
    fn dim(&self, d: Dim) -> Result<String> {
        Ok(match d {
            Dim::Zero => "0".into(),
            Dim::One => "1".into(),
            Dim::Var(x) => format!(
                "i{}",
                self.dims
                    .iter()
                    .position(|y| *y == x)
                    .ok_or_else(|| Error::plain("internal error: escaped interval variable"))?
            ),
        })
    }
}
#[derive(Clone, PartialEq, Eq, Hash)]
struct QuoteKey {
    v: ValId,
    ty: Option<ValId>,
    face: FaceId,
    terms: Vec<u32>,
    dims: Vec<u32>,
}
enum Work {
    Finish(QuoteKey, usize, usize),
    Quote(ValId, Option<ValId>, FaceId),
    Text(String),
    Face(FaceId),
    Term(u32),
    EndTerm,
    Dim(u32),
    EndDim,
}
fn text(s: impl Into<String>) -> Work {
    Work::Text(s.into())
}
impl Engine<'_> {
    pub fn quote(
        &mut self,
        v: ValId,
        ty: ValId,
        face: FaceId,
        max_output: usize,
        max_work: usize,
    ) -> Result<String> {
        use Work::*;
        let mut pending = vec![Quote(v, Some(ty), face)];
        let mut names = Names::default();
        let mut out = String::new();
        let mut next_sample = 65536;
        let mut memo = crate::hash::IdMap::<QuoteKey, (usize, usize)>::default();
        let mut large_memo: Vec<(QuoteKey, usize, usize)> = Vec::new();
        let mut congruence_hits = 0usize;
        let mut memo_hits = 0usize;
        let mut memo_bytes = 0usize;
        let result = (|| {
            while !pending.is_empty() {
                if self.should_collect() {
                    let mut roots = Vec::new();
                    for w in &pending {
                        if let Quote(v, t, _) = w {
                            roots.push(*v);
                            roots.extend(t);
                        }
                    }
                    let mut faces = Vec::new();
                    for w in &pending {
                        match w {
                            Quote(_, _, f) | Face(f) => faces.push(*f),
                            _ => {}
                        }
                    }
                    self.collect_quote(&mut roots, &mut faces);
                    let mut faces = faces.into_iter();
                    for w in &mut pending {
                        match w {
                            Quote(_, _, f) | Face(f) => *f = faces.next().unwrap(),
                            _ => {}
                        }
                    }
                    memo.clear();
                    large_memo.clear();
                    let mut roots = roots.into_iter();
                    for w in &mut pending {
                        if let Quote(v, t, _) = w {
                            *v = roots.next().unwrap();
                            if let Some(t) = t {
                                *t = roots.next().unwrap();
                            }
                        }
                    }
                }
                let work = pending.pop().unwrap();
                if out.len() >= next_sample {
                    self.profile_snapshot(out.len());
                    next_sample += 65536;
                }
                self.tick()?;
                let mut next = Vec::new();
                match work {
                    Finish(key, start, generation) => {
                        if generation == self.collections
                            && memo.len() < 16384
                            && out.len() - start >= 128
                        {
                            if out.len() - start >= 4096 {
                                if large_memo.len() >= 64 {
                                    large_memo.remove(0);
                                }
                                large_memo.push((key.clone(), start, out.len()));
                            }
                            memo.insert(key, (start, out.len()));
                        }
                    }
                    Text(s) => {
                        if s.len() > max_output.saturating_sub(out.len()) {
                            return Err(Error::plain("quotation output byte budget exhausted"));
                        }
                        out.try_reserve(s.len())
                            .map_err(|_| Error::plain("quotation output allocation failed"))?;
                        out.push_str(&s);
                    }
                    Term(x) => names.terms.push(x),
                    EndTerm => {
                        names.terms.pop();
                    }
                    Dim(i) => names.dims.push(i),
                    EndDim => {
                        names.dims.pop();
                    }
                    Face(f) => match self.faces.get(f) {
                        crate::face::Face::Top => next.push(text("top")),
                        crate::face::Face::Bot => next.push(text("bottom")),
                        crate::face::Face::Eq(a, b) => {
                            next.push(text(format!("(= {} {})", names.dim(a)?, names.dim(b)?)))
                        }
                        crate::face::Face::And(a, b) | crate::face::Face::Or(a, b) => {
                            let op = if matches!(self.faces.get(f), crate::face::Face::And(..)) {
                                "and"
                            } else {
                                "or"
                            };
                            next.extend([
                                text(format!("({op} ")),
                                Face(a),
                                text(" "),
                                Face(b),
                                text(")"),
                            ]);
                        }
                    },
                    Quote(v, ty, face) => {
                        let mut v = self.force(v, face)?;
                        if self.optimized_quote()
                            && let Val::Com(mut c) = self.get(v)
                        {
                            let i = self.quote_dimension(&mut names);
                            c.family = self.restrict(c.family, c.dim, crate::face::Dim::Var(i));
                            c.tubes = c
                                .tubes
                                .into_iter()
                                .map(|(f, t)| {
                                    (f, self.restrict(t, c.dim, crate::face::Dim::Var(i)))
                                })
                                .collect();
                            c.dim = i;
                            v = self.alloc(Val::Com(c));
                        }
                        let key = QuoteKey {
                            v,
                            ty,
                            face,
                            terms: names.terms.clone(),
                            dims: names.dims.clone(),
                        };
                        let mut found = memo.get(&key).copied();
                        if found.is_none()
                            && self.optimized_quote()
                            && matches!(self.get(v), Val::Com(_))
                        {
                            for (old, start, end) in large_memo
                                .iter()
                                .rev()
                                .filter(|(k, _, _)| {
                                    k.ty == ty
                                        && k.face == face
                                        && k.terms == names.terms
                                        && k.dims == names.dims
                                })
                                .take(4)
                            {
                                if self.same(v, old.v, face, 64)? {
                                    found = Some((*start, *end));
                                    congruence_hits += 1;
                                    break;
                                }
                            }
                        }
                        if self.optimized_quote()
                            && let Some((start, end)) = found
                        {
                            let len = end - start;
                            if len > max_output.saturating_sub(out.len()) {
                                return Err(Error::plain("quotation output byte budget exhausted"));
                            }
                            out.try_reserve(len)
                                .map_err(|_| Error::plain("quotation output allocation failed"))?;
                            out.extend_from_within(start..end);
                            memo_hits += 1;
                            memo_bytes += len;
                        } else {
                            next = self.quote_work(v, ty, face, &mut names)?;
                            if self.optimized_quote() {
                                next.push(Finish(key, out.len(), self.collections));
                            }
                        }
                    }
                }
                if next.len() > max_work.saturating_sub(pending.len()) {
                    return Err(Error::plain("quotation pending-work budget exhausted"));
                }
                pending
                    .try_reserve(next.len())
                    .map_err(|_| Error::plain("quotation work allocation failed"))?;
                pending.extend(next.into_iter().rev());
            }
            Ok(())
        })();
        self.profile_snapshot(out.len());
        if std::env::var_os("KAMO_PROFILE").is_some() {
            eprintln!(
                "QUOTE congruence_hits={congruence_hits} memo_hits={memo_hits} memo_bytes={memo_bytes} bytes={}",
                out.len()
            );
        }
        if result.is_err()
            && let Some(path) = std::env::var_os("KAMO_PROFILE_PREFIX")
        {
            std::fs::write(path, &out)
                .map_err(|e| Error::plain(format!("cannot write diagnostic prefix: {e}")))?;
        }
        result.map_err(|mut e| {
            e.message = format!(
                "{} (during quotation: {} bytes emitted, {} pending tasks, {} steps; faces={})",
                e.message,
                out.len(),
                pending.len(),
                self.steps,
                self.faces.len()
            );
            e
        })?;
        Ok(out)
    }
    fn quote_dimension(&mut self, n: &mut Names) -> u32 {
        let depth = n.dims.len();
        while n.dim_levels.len() <= depth {
            n.dim_levels.push(self.fresh_dim());
        }
        n.dim_levels[depth]
    }
    fn quote_work(
        &mut self,
        v: ValId,
        ty: Option<ValId>,
        face: FaceId,
        n: &mut Names,
    ) -> Result<Vec<Work>> {
        use Work::*;
        let q = |v, ty| Quote(v, ty, face);
        let term_name = format!("x{}", n.terms.len());
        let dim_name = format!("i{}", n.dims.len());
        if let Some(ty) = ty {
            let ty = self.force(ty, face)?;
            match self.get(ty) {
                Val::Pi(a, b) => {
                    let x = self.variable(a);
                    let Val::Var(level, _) = self.get(x) else {
                        unreachable!()
                    };
                    let body = self.app(v, x);
                    let cod = self.inst(&b, x);
                    return Ok(vec![
                        text(format!("(lam {term_name} ")),
                        Term(level),
                        q(body, Some(cod)),
                        EndTerm,
                        text(")"),
                    ]);
                }
                Val::Sigma(a, b) => {
                    let x = self.fst(v);
                    let y = self.snd(v);
                    let cod = self.inst(&b, x);
                    return Ok(vec![
                        text("(pair "),
                        q(x, Some(a)),
                        text(" "),
                        q(y, Some(cod)),
                        text(")"),
                    ]);
                }
                Val::Path(b, _, _) => {
                    let i = self.quote_dimension(n);
                    let body = self.at(v, crate::face::Dim::Var(i));
                    let cod = self.inst_dim(&b, crate::face::Dim::Var(i));
                    return Ok(vec![
                        text(format!("(path {dim_name} ")),
                        Dim(i),
                        q(body, Some(cod)),
                        EndDim,
                        text(")"),
                    ]);
                }
                Val::Glue(base, bs) => {
                    let unglued = self.alloc(Val::Unglue(ty, v));
                    let mut tasks = vec![
                        text("(glue "),
                        q(ty, None),
                        text(" "),
                        q(unglued, Some(base)),
                        text(" ("),
                    ];
                    let mut first = true;
                    for (f, a, _) in bs {
                        let under = self.faces.and(face, f);
                        if self.faces.inconsistent(under)? {
                            continue;
                        }
                        if !first {
                            tasks.push(text(" "));
                        }
                        first = false;
                        tasks.extend([
                            text("("),
                            Face(f),
                            text(" "),
                            Quote(v, Some(a), under),
                            text(")"),
                        ]);
                    }
                    tasks.push(text("))"));
                    return Ok(tasks);
                }
                _ => {}
            }
        }
        let v = self.force(v, face)?;
        Ok(match self.get(v) {
            Val::Var(x, _) => vec![text(format!(
                "x{}",
                n.terms
                    .iter()
                    .position(|y| *y == x)
                    .ok_or_else(|| Error::plain("internal error: escaped term variable"))?
            ))],
            Val::U(l) => vec![text(format!("(U {l})"))],
            Val::Bool => vec![text("Bool")],
            Val::Nat => vec![text("Nat")],
            Val::True => vec![text("true")],
            Val::False => vec![text("false")],
            Val::Zero => vec![text("zero")],
            Val::Pi(a, b) | Val::Sigma(a, b) => {
                let op = if matches!(self.get(v), Val::Pi(..)) {
                    "Pi"
                } else {
                    "Sigma"
                };
                let x = self.variable(a);
                let Val::Var(level, _) = self.get(x) else {
                    unreachable!()
                };
                let body = self.inst(&b, x);
                vec![
                    text(format!("({op} {term_name} ")),
                    q(a, None),
                    text(" "),
                    Term(level),
                    q(body, None),
                    EndTerm,
                    text(")"),
                ]
            }
            Val::Path(b, l, r) => {
                let i = self.quote_dimension(n);
                let body = self.inst_dim(&b, crate::face::Dim::Var(i));
                let lt = self.inst_dim(&b, crate::face::Dim::Zero);
                let rt = self.inst_dim(&b, crate::face::Dim::One);
                vec![
                    text(format!("(Path {dim_name} ")),
                    Dim(i),
                    q(body, None),
                    EndDim,
                    text(" "),
                    q(l, Some(lt)),
                    text(" "),
                    q(r, Some(rt)),
                    text(")"),
                ]
            }
            Val::Suc(k) => {
                let nat = self.alloc(Val::Nat);
                vec![text("(suc "), q(k, Some(nat)), text(")")]
            }
            Val::App(f, a) => {
                let ft = self.neutral_type(f, face)?;
                let ft = self.force(ft, face)?;
                let at = if let Val::Pi(a, _) = self.get(ft) {
                    Some(a)
                } else {
                    None
                };
                vec![text("(app "), q(f, None), text(" "), q(a, at), text(")")]
            }
            Val::Fst(p) | Val::Snd(p) => vec![
                text(if matches!(self.get(v), Val::Fst(_)) {
                    "(fst "
                } else {
                    "(snd "
                }),
                q(p, None),
                text(")"),
            ],
            Val::PApp(p, d) => vec![text("(at "), q(p, None), text(format!(" {})", n.dim(d)?))],
            Val::If(p, a, b, c) => {
                let bt = self.alloc(Val::Bool);
                let x = self.variable(bt);
                let Val::Var(level, _) = self.get(x) else {
                    unreachable!()
                };
                let px = self.app(p, x);
                let tv = self.alloc(Val::True);
                let fv = self.alloc(Val::False);
                let at = self.app(p, tv);
                let bty = self.app(p, fv);
                vec![
                    text(format!("(bool-elim (lam {term_name} ")),
                    Term(level),
                    q(px, None),
                    EndTerm,
                    text(") "),
                    q(a, Some(at)),
                    text(" "),
                    q(b, Some(bty)),
                    text(" "),
                    q(c, Some(bt)),
                    text(")"),
                ]
            }
            Val::NatElim(p, z, s, k) => {
                let nat = self.alloc(Val::Nat);
                let x = self.variable(nat);
                let Val::Var(level, _) = self.get(x) else {
                    unreachable!()
                };
                let px = self.app(p, x);
                let ih = self.variable(px);
                let Val::Var(ihlevel, _) = self.get(ih) else {
                    unreachable!()
                };
                let ihname = format!("x{}", n.terms.len() + 1);
                let step = self.app(s, x);
                let step = self.app(step, ih);
                let suc = self.alloc(Val::Suc(x));
                let sty = self.app(p, suc);
                let zero = self.alloc(Val::Zero);
                let zty = self.app(p, zero);
                vec![
                    text(format!("(nat-elim (lam {term_name} ")),
                    Term(level),
                    q(px, None),
                    EndTerm,
                    text(") "),
                    q(z, Some(zty)),
                    text(format!(" (lam {term_name} (lam {ihname} ")),
                    Term(level),
                    Term(ihlevel),
                    q(step, Some(sty)),
                    EndTerm,
                    EndTerm,
                    text(")) "),
                    q(k, Some(nat)),
                    text(")"),
                ]
            }
            Val::Com(c) => {
                let from = n.dim(c.from)?;
                let to = n.dim(c.to)?;
                let src = self.restrict(c.family, c.dim, c.from);
                // The composition dimension scopes family and tubes, not cap.
                let mut tasks = vec![
                    text(format!("(com {dim_name} ")),
                    Dim(c.dim),
                    q(c.family, None),
                    EndDim,
                    text(format!(" {from} {to} ")),
                    q(c.cap, Some(src)),
                    text(" ("),
                    Dim(c.dim),
                ];
                let mut first = true;
                for (f, v) in c.tubes {
                    let under = self.faces.and(face, f);
                    if self.faces.inconsistent(under)? {
                        continue;
                    }
                    if !first {
                        tasks.push(text(" "));
                    }
                    first = false;
                    tasks.extend([
                        text("("),
                        Face(f),
                        text(" "),
                        Quote(v, Some(c.family), under),
                        text(")"),
                    ]);
                }
                tasks.extend([EndDim, text("))")]);
                tasks
            }
            Val::System(a, bs) => {
                let mut tasks = vec![text("(system "), q(a, None), text(" (")];
                let mut first = true;
                for (f, v) in bs {
                    let under = self.faces.and(face, f);
                    if self.faces.inconsistent(under)? {
                        continue;
                    }
                    if !first {
                        tasks.push(text(" "));
                    }
                    first = false;
                    tasks.extend([
                        text("("),
                        Face(f),
                        text(" "),
                        Quote(v, Some(a), under),
                        text(")"),
                    ]);
                }
                tasks.push(text("))"));
                tasks
            }
            Val::Glue(base, bs) => {
                let mut tasks = vec![text("(Glue "), q(base, None), text(" (")];
                let mut first = true;
                for (f, a, e) in bs {
                    let under = self.faces.and(face, f);
                    if self.faces.inconsistent(under)? {
                        continue;
                    }
                    if !first {
                        tasks.push(text(" "));
                    }
                    first = false;
                    let eqty = self.equiv_type(a, base);
                    tasks.extend([
                        text("("),
                        Face(f),
                        text(" "),
                        Quote(a, None, under),
                        text(" "),
                        Quote(e, Some(eqty), under),
                        text(")"),
                    ]);
                }
                tasks.push(text("))"));
                tasks
            }
            Val::Unglue(g, v) => vec![
                text("(unglue "),
                q(g, None),
                text(" "),
                q(v, None),
                text(")"),
            ],
            Val::GlueIntro(..) | Val::Lam(_) | Val::PLam(_) | Val::Pair(..) => {
                return Err(Error::plain(
                    "internal error: quotation needs an introduction form's type",
                ));
            }
            Val::Susp(..) | Val::Sub(..) => unreachable!("force removes suspension heads"),
        })
    }
}
