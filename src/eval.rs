//! Lazy semantic evaluation. Every cache key includes the face context.
use crate::arena::{Arena, Key, key};
use crate::face::{Dim, FaceId, Faces};
use crate::hash::IdMap as HashMap;
use crate::syntax::{D, F, Program, Term, TermId};
use crate::{Error, Result, Statistics};
key!(ValId);
key!(EnvId);
key!(SubId);

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct Env {
    pub terms: Vec<ValId>,
    pub dims: Vec<Dim>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
struct Sub {
    terms: Vec<(u32, ValId)>,
    dims: Vec<(u32, Dim)>,
    compose: Option<(SubId, SubId)>,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Binder {
    pub var: u32,
    pub body: ValId,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Composition {
    pub dim: u32,
    pub family: ValId,
    pub from: Dim,
    pub to: Dim,
    pub cap: ValId,
    pub tubes: Vec<(FaceId, ValId)>,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Val {
    Susp(TermId, EnvId),
    Sub(ValId, SubId),
    Var(u32, Option<ValId>),
    U(u32),
    Pi(ValId, Binder),
    Sigma(ValId, Binder),
    Lam(Binder),
    App(ValId, ValId),
    Pair(ValId, ValId),
    Fst(ValId),
    Snd(ValId),
    Bool,
    True,
    False,
    Nat,
    Zero,
    Suc(ValId),
    If(ValId, ValId, ValId, ValId),
    NatElim(ValId, ValId, ValId, ValId),
    Path(Binder, ValId, ValId),
    PLam(Binder),
    PApp(ValId, Dim),
    Com(Composition),
    System(ValId, Vec<(FaceId, ValId)>),
    Glue(ValId, Vec<(FaceId, ValId, ValId)>),
    GlueIntro(ValId, Vec<(FaceId, ValId)>),
    Unglue(ValId, ValId),
}
#[derive(Default)]
struct Profile {
    sites: std::collections::BTreeMap<(&'static str, u32), usize>,
    unfolds: std::collections::BTreeMap<usize, usize>,
    pushes: usize,
}
pub(crate) struct Engine<'a> {
    profile: Option<Profile>,
    support_cache: HashMap<ValId, Option<support::Support>>,
    computing_support: bool,
    pub collections: usize,
    collection_at: usize,
    pub reclaimed_nodes: usize,
    pub allocated_values: usize,
    capture_cache: HashMap<TermId, crate::capture::Slots>,
    push_cache: HashMap<(ValId, SubId), ValId>,
    pub program: &'a Program,
    values: Arena<ValId, Val>,
    envs: Arena<EnvId, Env>,
    subs: Arena<SubId, Sub>,
    pub faces: Faces,
    cache: HashMap<(ValId, FaceId, bool), ValId>,
    globals: HashMap<usize, ValId>,
    next_term: u32,
    next_dim: u32,
    pub steps: u64,
    fuel: u64,
    optimized: bool,
    max_nodes: usize,
    sub_cache: HashMap<(ValId, SubId), ValId>,
    value_intern: HashMap<Val, ValId>,
    env_intern: HashMap<Env, EnvId>,
    sub_intern: HashMap<Sub, SubId>,
    unfold_cache: HashMap<(TermId, EnvId), ValId>,
}
impl<'a> Engine<'a> {
    pub fn new(program: &'a Program, optimized: bool, fuel: u64, max_nodes: usize) -> Self {
        Self {
            support_cache: HashMap::default(),
            computing_support: false,
            collections: 0,
            collection_at: (max_nodes / 2).clamp(1, 250_000),
            reclaimed_nodes: 0,
            allocated_values: 0,
            capture_cache: HashMap::default(),
            push_cache: HashMap::default(),
            profile: std::env::var_os("KAMO_PROFILE").map(|_| Profile::default()),
            program,
            values: Arena::default(),
            envs: Arena::default(),
            subs: Arena::default(),
            faces: Faces::default(),
            cache: HashMap::default(),
            globals: HashMap::default(),
            next_term: 0,
            next_dim: 0,
            steps: 0,
            fuel,
            optimized,
            max_nodes,
            sub_cache: HashMap::default(),
            value_intern: HashMap::default(),
            env_intern: HashMap::default(),
            sub_intern: HashMap::default(),
            unfold_cache: HashMap::default(),
        }
    }
    pub fn tick(&mut self) -> Result<()> {
        if self.values.len() + self.envs.len() + self.subs.len() + self.faces.len() > self.max_nodes
        {
            return Err(Error::plain(
                "arena node budget exhausted; computation stopped before further evaluation",
            ));
        }
        if self.steps >= self.fuel {
            return Err(Error::plain(
                "evaluation budget exhausted (not a proof rejection); increase --fuel",
            ));
        }
        self.steps += 1;
        Ok(())
    }
    #[track_caller]
    pub fn alloc(&mut self, v: Val) -> ValId {
        if self.optimized {
            if let Some(id) = self.value_intern.get(&v) {
                return *id;
            }
            if let Some(p) = &mut self.profile {
                let l = std::panic::Location::caller();
                *p.sites.entry((l.file(), l.line())).or_default() += 1;
            }
            self.allocated_values += 1;
            let id = self.values.alloc(v.clone());
            self.value_intern.insert(v, id);
            id
        } else {
            self.allocated_values += 1;
            self.values.alloc(v)
        }
    }
    pub fn get(&self, v: ValId) -> Val {
        self.values.get(v).clone()
    }
    pub fn env(&mut self, e: Env) -> EnvId {
        if self.optimized {
            if let Some(id) = self.env_intern.get(&e) {
                return *id;
            }
            let id = self.envs.alloc(e.clone());
            self.env_intern.insert(e, id);
            id
        } else {
            self.envs.alloc(e)
        }
    }
    fn substitution(&mut self, s: Sub) -> SubId {
        if self.optimized {
            if let Some(id) = self.sub_intern.get(&s) {
                return *id;
            }
            let id = self.subs.alloc(s.clone());
            self.sub_intern.insert(s, id);
            id
        } else {
            self.subs.alloc(s)
        }
    }
    pub fn environment(&self, e: EnvId) -> Env {
        self.envs.get(e).clone()
    }
    pub fn fresh_term(&mut self) -> u32 {
        let n = self.next_term;
        self.next_term += 1;
        n
    }
    pub fn fresh_dim(&mut self) -> u32 {
        let n = self.next_dim;
        self.next_dim += 1;
        n
    }
    pub fn variable(&mut self, ty: ValId) -> ValId {
        let v = self.fresh_term();
        self.alloc(Val::Var(v, Some(ty)))
    }
    pub fn thunk(&mut self, t: TermId, e: EnvId) -> ValId {
        if self.optimized {
            let simple = match self.program.terms.get(t).term {
                Term::Var(i) => {
                    let env = self.envs.get(e);
                    return env.terms[env.terms.len() - 1 - i];
                }
                Term::U(l) => Some(Val::U(l)),
                Term::Bool => Some(Val::Bool),
                Term::Nat => Some(Val::Nat),
                Term::True => Some(Val::True),
                Term::False => Some(Val::False),
                Term::Zero => Some(Val::Zero),
                _ => None,
            };
            if let Some(v) = simple {
                return self.alloc(v);
            }
        }
        let e = if self.optimized {
            let (ts, ds) = crate::capture::slots(self.program, t, &mut self.capture_cache);
            let mut env = self.environment(e);
            let tn = ts.last().map_or(0, |i| i + 1);
            let dn = ds.last().map_or(0, |i| i + 1);
            env.terms.drain(..env.terms.len() - tn);
            env.dims.drain(..env.dims.len() - dn);
            if tn > 0 {
                let unused = self.alloc(Val::Zero);
                for i in 0..tn {
                    if ts.binary_search(&i).is_err() {
                        env.terms[tn - 1 - i] = unused;
                    }
                }
            }
            for i in 0..dn {
                if ds.binary_search(&i).is_err() {
                    env.dims[dn - 1 - i] = Dim::Zero;
                }
            }
            self.env(env)
        } else {
            e
        };
        self.alloc(Val::Susp(t, e))
    }
    pub fn dim(&self, d: D, e: EnvId) -> Dim {
        match d {
            D::Zero => Dim::Zero,
            D::One => Dim::One,
            D::Bound(i) => {
                let ds = &self.envs.get(e).dims;
                ds[ds.len() - 1 - i]
            }
        }
    }
    pub fn face(&mut self, f: &F, e: EnvId) -> FaceId {
        match f {
            F::Top => self.faces.top(),
            F::Bot => self.faces.bot(),
            F::Eq(a, b) => self.faces.eq(self.dim(*a, e), self.dim(*b, e)),
            F::And(a, b) => {
                let a = self.face(a, e);
                let b = self.face(b, e);
                self.faces.and(a, b)
            }
            F::Or(a, b) => {
                let a = self.face(a, e);
                let b = self.face(b, e);
                self.faces.or(a, b)
            }
        }
    }
    fn term_binder(&mut self, t: TermId, e: EnvId, ty: Option<ValId>) -> Binder {
        let var = self.fresh_term();
        let v = self.alloc(Val::Var(var, ty));
        let mut env = self.environment(e);
        env.terms.push(v);
        let env = self.env(env);
        Binder {
            var,
            body: self.thunk(t, env),
        }
    }
    fn dim_binder(&mut self, t: TermId, e: EnvId) -> Binder {
        let var = self.fresh_dim();
        let mut env = self.environment(e);
        env.dims.push(Dim::Var(var));
        let env = self.env(env);
        Binder {
            var,
            body: self.thunk(t, env),
        }
    }
    pub fn inst(&mut self, b: &Binder, x: ValId) -> ValId {
        let s = self.substitution(Sub {
            terms: vec![(b.var, x)],
            dims: vec![],
            compose: None,
        });
        self.sub(b.body, s)
    }
    pub fn inst_dim(&mut self, b: &Binder, d: Dim) -> ValId {
        self.restrict(b.body, b.var, d)
    }
    pub fn restrict(&mut self, v: ValId, x: u32, d: Dim) -> ValId {
        if d == Dim::Var(x) {
            return v;
        }
        let s = self.substitution(Sub {
            terms: vec![],
            dims: vec![(x, d)],
            compose: None,
        });
        self.sub(v, s)
    }
    fn sub(&mut self, v: ValId, s: SubId) -> ValId {
        if self.optimized
            && let Some(w) = self.sub_cache.get(&(v, s))
        {
            return *w;
        }
        let w = self.sub_uncached(v, s);
        if self.optimized {
            self.sub_cache.insert((v, s), w);
        }
        w
    }
    fn sub_uncached(&mut self, v: ValId, s: SubId) -> ValId {
        if self.optimized && !self.computing_support && self.irrelevant(v, s) {
            return v;
        }
        if self.optimized {
            match self.get(v) {
                Val::Pair(a, b) => {
                    let a = self.sub(a, s);
                    let b = self.sub(b, s);
                    return self.alloc(Val::Pair(a, b));
                }
                Val::Var(x, ty) => {
                    if let Some(image) = self.sub_term(s, x) {
                        return image;
                    }
                    let ty = ty.map(|t| self.sub(t, s));
                    return self.alloc(Val::Var(x, ty));
                }
                Val::U(_) | Val::Bool | Val::Nat | Val::True | Val::False | Val::Zero => return v,
                Val::Susp(t, e)
                    if matches!(self.program.terms.get(t).term, Term::Global(_))
                        || (self.envs.get(e).terms.is_empty()
                            && self.envs.get(e).dims.is_empty()) =>
                {
                    return v;
                }
                _ => {}
            }
            if let Val::Sub(v, old) = self.get(v) {
                let s = self.substitution(Sub {
                    terms: vec![],
                    dims: vec![],
                    compose: Some((old, s)),
                });
                return self.alloc(Val::Sub(v, s));
            }
        }
        self.alloc(Val::Sub(v, s))
    }
    fn sub_dim(&self, s: SubId, d: Dim) -> Dim {
        let sub = self.subs.get(s);
        if let Some((a, b)) = sub.compose {
            return self.sub_dim(b, self.sub_dim(a, d));
        }
        if let Dim::Var(v) = d {
            sub.dims
                .iter()
                .find(|(x, _)| *x == v)
                .map(|(_, d)| *d)
                .unwrap_or(d)
        } else {
            d
        }
    }
    fn sub_term(&mut self, s: SubId, x: u32) -> Option<ValId> {
        let sub = self.subs.get(s).clone();
        if let Some((a, b)) = sub.compose {
            return if let Some(v) = self.sub_term(a, x) {
                Some(self.sub(v, b))
            } else {
                self.sub_term(b, x)
            };
        }
        sub.terms.iter().find(|(y, _)| *y == x).map(|(_, v)| *v)
    }
    fn renamed(&mut self, old: u32, new: u32, s: SubId, dim: bool) -> SubId {
        let rename = if dim {
            Sub {
                terms: vec![],
                dims: vec![(old, Dim::Var(new))],
                compose: None,
            }
        } else {
            let v = self.alloc(Val::Var(new, None));
            Sub {
                terms: vec![(old, v)],
                dims: vec![],
                compose: None,
            }
        };
        let rename = self.substitution(rename);
        self.substitution(Sub {
            terms: vec![],
            dims: vec![],
            compose: Some((rename, s)),
        })
    }
    fn sub_binder(&mut self, b: Binder, s: SubId, dim: bool) -> Binder {
        let var = if dim {
            self.fresh_dim()
        } else {
            self.fresh_term()
        };
        let s = self.renamed(b.var, var, s, dim);
        Binder {
            var,
            body: self.sub(b.body, s),
        }
    }
    fn sub_face(&mut self, f: FaceId, s: SubId) -> FaceId {
        let dims = self.faces.dimensions(f);
        let map = dims
            .into_iter()
            .map(|d| (d, self.sub_dim(s, d)))
            .collect::<HashMap<_, _>>();
        self.faces
            .substitute(f, &|d| map.get(&d).copied().unwrap_or(d))
    }
    pub fn restrict_face(&mut self, f: FaceId, x: u32, d: Dim) -> FaceId {
        self.faces
            .substitute(f, &|v| if v == Dim::Var(x) { d } else { v })
    }
    fn push(&mut self, v: ValId, s: SubId) -> ValId {
        if self.optimized
            && let Some(w) = self.push_cache.get(&(v, s))
        {
            return *w;
        }
        let w = self.push_uncached(v, s);
        if self.optimized {
            self.push_cache.insert((v, s), w);
        }
        w
    }
    fn push_uncached(&mut self, v: ValId, s: SubId) -> ValId {
        if let Some(p) = &mut self.profile {
            p.pushes += 1;
        }
        let out = match self.get(v) {
            Val::Sub(v, t) => {
                let inner = self.push(v, t);
                return self.sub(inner, s);
            }
            Val::Susp(t, e) => {
                let env = self.environment(e);
                let terms = env.terms.into_iter().map(|v| self.sub(v, s)).collect();
                let dims = env.dims.into_iter().map(|d| self.sub_dim(s, d)).collect();
                let e = self.env(Env { terms, dims });
                return self.thunk(t, e);
            }
            Val::Var(x, ty) => {
                if let Some(v) = self.sub_term(s, x) {
                    return v;
                }
                Val::Var(x, ty.map(|t| self.sub(t, s)))
            }
            Val::U(_) | Val::Bool | Val::Nat | Val::True | Val::False | Val::Zero => return v,
            Val::Pi(a, b) => {
                let a = self.sub(a, s);
                let b = self.sub_binder(b, s, false);
                Val::Pi(a, b)
            }
            Val::Sigma(a, b) => {
                let a = self.sub(a, s);
                let b = self.sub_binder(b, s, false);
                Val::Sigma(a, b)
            }
            Val::Lam(b) => Val::Lam(self.sub_binder(b, s, false)),
            Val::PLam(b) => Val::PLam(self.sub_binder(b, s, true)),
            Val::Path(b, l, r) => {
                let b = self.sub_binder(b, s, true);
                Val::Path(b, self.sub(l, s), self.sub(r, s))
            }
            Val::App(a, b) => Val::App(self.sub(a, s), self.sub(b, s)),
            Val::Pair(a, b) => Val::Pair(self.sub(a, s), self.sub(b, s)),
            Val::Fst(a) => Val::Fst(self.sub(a, s)),
            Val::Snd(a) => Val::Snd(self.sub(a, s)),
            Val::Suc(a) => Val::Suc(self.sub(a, s)),
            Val::If(p, a, b, c) => Val::If(
                self.sub(p, s),
                self.sub(a, s),
                self.sub(b, s),
                self.sub(c, s),
            ),
            Val::NatElim(p, a, b, c) => Val::NatElim(
                self.sub(p, s),
                self.sub(a, s),
                self.sub(b, s),
                self.sub(c, s),
            ),
            Val::PApp(p, d) => Val::PApp(self.sub(p, s), self.sub_dim(s, d)),
            Val::System(a, bs) => {
                let a = self.sub(a, s);
                let bs = bs
                    .into_iter()
                    .map(|(f, v)| (self.sub_face(f, s), self.sub(v, s)))
                    .collect();
                Val::System(a, bs)
            }
            Val::Glue(a, bs) => {
                let a = self.sub(a, s);
                let bs = bs
                    .into_iter()
                    .map(|(f, t, e)| (self.sub_face(f, s), self.sub(t, s), self.sub(e, s)))
                    .collect();
                Val::Glue(a, bs)
            }
            Val::GlueIntro(a, bs) => {
                let a = self.sub(a, s);
                let bs = bs
                    .into_iter()
                    .map(|(f, t)| (self.sub_face(f, s), self.sub(t, s)))
                    .collect();
                Val::GlueIntro(a, bs)
            }
            Val::Unglue(g, v) => Val::Unglue(self.sub(g, s), self.sub(v, s)),
            Val::Com(c) => {
                let dim = self.fresh_dim();
                let inner = self.renamed(c.dim, dim, s, true);
                Val::Com(Composition {
                    dim,
                    family: self.sub(c.family, inner),
                    from: self.sub_dim(s, c.from),
                    to: self.sub_dim(s, c.to),
                    cap: self.sub(c.cap, s),
                    tubes: c
                        .tubes
                        .into_iter()
                        .map(|(f, v)| (self.sub_face(f, s), self.sub(v, inner)))
                        .collect(),
                })
            }
        };
        self.alloc(out)
    }
    fn unfold(&mut self, t: TermId, e: EnvId) -> ValId {
        if self.optimized
            && let Some(v) = self.unfold_cache.get(&(t, e))
        {
            return *v;
        }
        let v = self.unfold_uncached(t, e);
        if self.optimized {
            self.unfold_cache.insert((t, e), v);
        }
        v
    }
    fn unfold_uncached(&mut self, t: TermId, e: EnvId) -> ValId {
        if let Some(p) = &mut self.profile {
            *p.unfolds
                .entry(self.program.terms.get(t).offset)
                .or_default() += 1;
        }
        let val = match self.program.terms.get(t).term.clone() {
            Term::Var(i) => {
                let ts = &self.envs.get(e).terms;
                return ts[ts.len() - 1 - i];
            }
            Term::Global(i) => {
                if let Some(v) = self.globals.get(&i) {
                    return *v;
                }
                let env = self.env(Env::default());
                let v = self.thunk(self.program.decls[i].body, env);
                self.globals.insert(i, v);
                return v;
            }
            Term::U(n) => Val::U(n),
            Term::Bool => Val::Bool,
            Term::True => Val::True,
            Term::False => Val::False,
            Term::Nat => Val::Nat,
            Term::Zero => Val::Zero,
            Term::Pi(a, b) => {
                let a = self.thunk(a, e);
                let b = self.term_binder(b, e, Some(a));
                Val::Pi(a, b)
            }
            Term::Sigma(a, b) => {
                let a = self.thunk(a, e);
                let b = self.term_binder(b, e, Some(a));
                Val::Sigma(a, b)
            }
            Term::Lam(b) => Val::Lam(self.term_binder(b, e, None)),
            Term::PLam(b) => Val::PLam(self.dim_binder(b, e)),
            Term::App(a, b) => Val::App(self.thunk(a, e), self.thunk(b, e)),
            Term::Pair(a, b) => Val::Pair(self.thunk(a, e), self.thunk(b, e)),
            Term::Fst(a) => Val::Fst(self.thunk(a, e)),
            Term::Snd(a) => Val::Snd(self.thunk(a, e)),
            Term::Suc(a) => Val::Suc(self.thunk(a, e)),
            Term::Ann(a, _) => return self.thunk(a, e),
            Term::If(p, a, b, c) => Val::If(
                self.thunk(p, e),
                self.thunk(a, e),
                self.thunk(b, e),
                self.thunk(c, e),
            ),
            Term::NatElim(p, a, b, c) => Val::NatElim(
                self.thunk(p, e),
                self.thunk(a, e),
                self.thunk(b, e),
                self.thunk(c, e),
            ),
            Term::Path(a, l, r) => {
                let b = self.dim_binder(a, e);
                Val::Path(b, self.thunk(l, e), self.thunk(r, e))
            }
            Term::PApp(a, d) => Val::PApp(self.thunk(a, e), self.dim(d, e)),
            Term::Com {
                family,
                from,
                to,
                cap,
                tubes,
            } => {
                let b = self.dim_binder(family, e);
                let mut env = self.environment(e);
                env.dims.push(Dim::Var(b.var));
                let extended = self.env(env);
                Val::Com(Composition {
                    dim: b.var,
                    family: b.body,
                    from: self.dim(from, e),
                    to: self.dim(to, e),
                    cap: self.thunk(cap, e),
                    tubes: tubes
                        .into_iter()
                        .map(|(f, t)| (self.face(&f, e), self.thunk(t, extended)))
                        .collect(),
                })
            }
            Term::System(a, bs) => Val::System(
                self.thunk(a, e),
                bs.into_iter()
                    .map(|(f, t)| (self.face(&f, e), self.thunk(t, e)))
                    .collect(),
            ),
            Term::Glue(a, bs) => Val::Glue(
                self.thunk(a, e),
                bs.into_iter()
                    .map(|(f, t, q)| (self.face(&f, e), self.thunk(t, e), self.thunk(q, e)))
                    .collect(),
            ),
            Term::GlueIntro(_, a, bs) => Val::GlueIntro(
                self.thunk(a, e),
                bs.into_iter()
                    .map(|(f, t)| (self.face(&f, e), self.thunk(t, e)))
                    .collect(),
            ),
            Term::Unglue(g, v) => Val::Unglue(self.thunk(g, e), self.thunk(v, e)),
        };
        self.alloc(val)
    }
    pub fn app(&mut self, f: ValId, a: ValId) -> ValId {
        self.alloc(Val::App(f, a))
    }
    pub fn fst(&mut self, p: ValId) -> ValId {
        if self.optimized
            && let Val::Pair(a, _) = self.get(p)
        {
            return a;
        }
        self.alloc(Val::Fst(p))
    }
    pub fn snd(&mut self, p: ValId) -> ValId {
        if self.optimized
            && let Val::Pair(_, b) = self.get(p)
        {
            return b;
        }
        self.alloc(Val::Snd(p))
    }
    pub fn at(&mut self, p: ValId, d: Dim) -> ValId {
        self.alloc(Val::PApp(p, d))
    }
    // Expose ordinary beta redexes without expanding Kan operations. This is
    // used only as a sufficient congruence shortcut, never as a normalizer.
    fn beta_head(&mut self, mut v: ValId) -> Result<ValId> {
        loop {
            self.tick()?;
            v = match self.get(v) {
                Val::Susp(t, e) => self.unfold(t, e),
                Val::Sub(w, s) => self.push(w, s),
                Val::App(f, a) => {
                    let f = self.beta_head(f)?;
                    if let Val::Lam(b) = self.get(f) {
                        self.inst(&b, a)
                    } else {
                        return Ok(self.alloc(Val::App(f, a)));
                    }
                }
                Val::Fst(p) => {
                    let p = self.beta_head(p)?;
                    if let Val::Pair(a, _) = self.get(p) {
                        a
                    } else {
                        return Ok(self.alloc(Val::Fst(p)));
                    }
                }
                Val::Snd(p) => {
                    let p = self.beta_head(p)?;
                    if let Val::Pair(_, b) = self.get(p) {
                        b
                    } else {
                        return Ok(self.alloc(Val::Snd(p)));
                    }
                }
                Val::PApp(p, d) => {
                    let p = self.beta_head(p)?;
                    if let Val::PLam(b) = self.get(p) {
                        self.inst_dim(&b, d)
                    } else {
                        return Ok(self.alloc(Val::PApp(p, d)));
                    }
                }
                _ => return Ok(v),
            };
        }
    }
    /// A sufficient syntactic equality check before unfolding definitions.
    /// Failure is inconclusive; ordinary typed conversion is still required.
    pub fn same(&mut self, a: ValId, b: ValId, face: FaceId, depth: usize) -> Result<bool> {
        self.tick()?;
        if a == b {
            return Ok(true);
        }
        if depth == 0 {
            return Ok(false);
        }
        let depth = depth - 1;
        match (self.get(a), self.get(b)) {
            (Val::Susp(t, _), Val::Susp(u, _)) if matches!((&self.program.terms.get(t).term,&self.program.terms.get(u).term),(Term::Global(i),Term::Global(j)) if i==j) => {
                Ok(true)
            }
            // Apply substitutions before consulting the ambient face. Cancelling
            // a shared substitution is invalid when it changes that face.
            (Val::Sub(v, s), _) => {
                let v = self.push(v, s);
                self.same(v, b, face, depth)
            }
            (_, Val::Sub(v, s)) => {
                let v = self.push(v, s);
                self.same(a, v, face, depth)
            }
            (Val::Susp(t, e), _) => {
                let v = self.unfold(t, e);
                self.same(v, b, face, depth)
            }
            (_, Val::Susp(t, e)) => {
                let v = self.unfold(t, e);
                self.same(a, v, face, depth)
            }
            (Val::Var(x, _), Val::Var(y, _)) => Ok(x == y),
            (Val::U(x), Val::U(y)) => Ok(x == y),
            (Val::Bool, Val::Bool)
            | (Val::Nat, Val::Nat)
            | (Val::Zero, Val::Zero)
            | (Val::True, Val::True)
            | (Val::False, Val::False) => Ok(true),
            (Val::App(f, x), Val::App(g, y))
            | (Val::Pair(f, x), Val::Pair(g, y))
            | (Val::Unglue(f, x), Val::Unglue(g, y)) => {
                Ok(self.same(f, g, face, depth)? && self.same(x, y, face, depth)?)
            }
            (Val::Fst(x), Val::Fst(y))
            | (Val::Snd(x), Val::Snd(y))
            | (Val::Suc(x), Val::Suc(y)) => self.same(x, y, face, depth),
            (Val::PApp(p, i), Val::PApp(q, j)) => {
                Ok(self.faces.equal(face, i, j)? && self.same(p, q, face, depth)?)
            }
            (Val::Lam(x), Val::Lam(y)) => {
                let var = self.fresh_term();
                let v = self.alloc(Val::Var(var, None));
                let x = self.inst(&x, v);
                let y = self.inst(&y, v);
                self.same(x, y, face, depth)
            }
            (Val::PLam(x), Val::PLam(y)) => {
                let i = self.fresh_dim();
                let x = self.inst_dim(&x, Dim::Var(i));
                let y = self.inst_dim(&y, Dim::Var(i));
                self.same(x, y, face, depth)
            }
            (Val::Pi(a, x), Val::Pi(b, y)) | (Val::Sigma(a, x), Val::Sigma(b, y)) => {
                if !self.same(a, b, face, depth)? {
                    return Ok(false);
                }
                let var = self.fresh_term();
                let v = self.alloc(Val::Var(var, None));
                let x = self.inst(&x, v);
                let y = self.inst(&y, v);
                self.same(x, y, face, depth)
            }
            (Val::Path(x, a, b), Val::Path(y, c, d)) => {
                if !self.same(a, c, face, depth)? || !self.same(b, d, face, depth)? {
                    return Ok(false);
                }
                let i = self.fresh_dim();
                let x = self.inst_dim(&x, Dim::Var(i));
                let y = self.inst_dim(&y, Dim::Var(i));
                self.same(x, y, face, depth)
            }
            (Val::Com(x), Val::Com(y)) => {
                if x.tubes.len() != y.tubes.len()
                    || !self.faces.equal(face, x.from, y.from)?
                    || !self.faces.equal(face, x.to, y.to)?
                    || !self.same(x.cap, y.cap, face, depth)?
                {
                    return Ok(false);
                }
                let i = self.fresh_dim();
                let d = Dim::Var(i);
                let a = self.restrict(x.family, x.dim, d);
                let b = self.restrict(y.family, y.dim, d);
                if !self.same(a, b, face, depth)? {
                    return Ok(false);
                }
                for ((f, a), (g, b)) in x.tubes.into_iter().zip(y.tubes) {
                    let f = self.faces.and(face, f);
                    let g = self.faces.and(face, g);
                    if !self.faces.entails(f, g)? || !self.faces.entails(g, f)? {
                        return Ok(false);
                    }
                    if self.faces.inconsistent(f)? {
                        continue;
                    }
                    let a = self.restrict(a, x.dim, d);
                    let b = self.restrict(b, y.dim, d);
                    if !self.same(a, b, f, depth)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => {
                let x = self.beta_head(a)?;
                let y = self.beta_head(b)?;
                if x == a && y == b {
                    Ok(false)
                } else {
                    self.same(x, y, face, depth)
                }
            }
        }
    }
    pub fn force(&mut self, original: ValId, face: FaceId) -> Result<ValId> {
        self.force_head(original, face, false)
    }
    pub fn force_glue(&mut self, original: ValId, face: FaceId) -> Result<ValId> {
        self.force_head(original, face, true)
    }
    fn force_head(&mut self, original: ValId, face: FaceId, preserve_glue: bool) -> Result<ValId> {
        self.tick()?;
        if self.optimized
            && let Some(v) = self.cache.get(&(original, face, preserve_glue))
        {
            return Ok(*v);
        }
        let mut v = original;
        loop {
            self.tick()?;
            let next = match self.get(v) {
                Val::Susp(t, e) => Some(self.unfold(t, e)),
                Val::Sub(a, s) => Some(self.push(a, s)),
                Val::App(f, a) => {
                    let f = self.force(f, face)?;
                    match self.get(f) {
                        Val::Lam(b) => Some(self.inst(&b, a)),
                        Val::System(ty, bs) => {
                            let pty = self.force(ty, face)?;
                            if let Val::Pi(_, b) = self.get(pty) {
                                let ty = self.inst(&b, a);
                                let bs = bs.into_iter().map(|(f, b)| (f, self.app(b, a))).collect();
                                Some(self.alloc(Val::System(ty, bs)))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                }
                Val::Fst(p) | Val::Snd(p) => {
                    let p = self.force(p, face)?;
                    match self.get(p) {
                        Val::Pair(a, b) => Some(if matches!(self.get(v), Val::Fst(_)) {
                            a
                        } else {
                            b
                        }),
                        _ => None,
                    }
                }
                Val::If(_, a, b, c) => {
                    let c = self.force(c, face)?;
                    match self.get(c) {
                        Val::True => Some(a),
                        Val::False => Some(b),
                        _ => None,
                    }
                }
                Val::NatElim(p, z, s, n) => {
                    let n = self.force(n, face)?;
                    match self.get(n) {
                        Val::Zero => Some(z),
                        Val::Suc(k) => {
                            let rec = self.alloc(Val::NatElim(p, z, s, k));
                            let step = self.app(s, k);
                            Some(self.app(step, rec))
                        }
                        _ => None,
                    }
                }
                Val::PApp(p, d) => {
                    let p = self.force(p, face)?;
                    if let Val::PLam(b) = self.get(p) {
                        Some(self.inst_dim(&b, d))
                    } else {
                        let ty = self.neutral_type(p, face)?;
                        let ty = self.force(ty, face)?;
                        if let Val::Path(_, l, r) = self.get(ty) {
                            if self.faces.equal(face, d, Dim::Zero)? {
                                Some(l)
                            } else if self.faces.equal(face, d, Dim::One)? {
                                Some(r)
                            } else {
                                None
                            }
                        } else {
                            return Err(Error::plain(
                                "internal error: path application has non-path type",
                            ));
                        }
                    }
                }
                Val::System(_, bs) => {
                    let mut selected = None;
                    for (f, v) in bs {
                        if self.faces.entails(face, f)? {
                            selected = Some(v);
                            break;
                        }
                    }
                    selected
                }
                Val::Glue(_, bs) if !preserve_glue => {
                    let mut selected = None;
                    for (f, v, _) in bs {
                        if self.faces.entails(face, f)? {
                            selected = Some(v);
                            break;
                        }
                    }
                    selected
                }
                Val::GlueIntro(_, bs) => {
                    let mut selected = None;
                    for (f, v) in bs {
                        if self.faces.entails(face, f)? {
                            selected = Some(v);
                            break;
                        }
                    }
                    selected
                }
                Val::Unglue(g, a) => {
                    let g = self.force_glue(g, face)?;
                    if let Val::Glue(_, bs) = self.get(g) {
                        let mut selected = None;
                        for (f, _, e) in bs {
                            if self.faces.entails(face, f)? {
                                selected = Some(e);
                                break;
                            }
                        }
                        if let Some(equiv) = selected {
                            let f = self.fst(equiv);
                            Some(self.app(f, a))
                        } else {
                            let a = self.force(a, face)?;
                            if let Val::GlueIntro(base, _) = self.get(a) {
                                Some(base)
                            } else {
                                None
                            }
                        }
                    } else {
                        return Err(Error::plain("internal error: unglue needs a Glue type"));
                    }
                }
                Val::Com(c) => {
                    // An explicit unglue annotation needs the Glue data even
                    // when universe composition restricts to its cap or tube.
                    // Ordinary forcing still applies the boundary rule first.
                    if preserve_glue {
                        let family = self.force(c.family, face)?;
                        if matches!(self.get(family), Val::U(_)) {
                            Some(self.compose_universe(c))
                        } else {
                            self.reduce_com(c, face)?
                        }
                    } else {
                        self.reduce_com(c, face)?
                    }
                }
                _ => None,
            };
            if let Some(n) = next {
                v = n;
            } else {
                break;
            }
        }
        if self.optimized {
            self.cache.insert((original, face, preserve_glue), v);
        }
        Ok(v)
    }
    pub fn neutral_type(&mut self, v: ValId, face: FaceId) -> Result<ValId> {
        let v = self.force(v, face)?;
        match self.get(v) {
            Val::Var(_, Some(ty)) => Ok(ty),
            Val::App(f, a) => {
                let ty = self.neutral_type(f, face)?;
                let ty = self.force(ty, face)?;
                if let Val::Pi(_, b) = self.get(ty) {
                    Ok(self.inst(&b, a))
                } else {
                    Err(Error::plain("internal error: neutral function type"))
                }
            }
            Val::Fst(p) | Val::Snd(p) => {
                let ty = self.neutral_type(p, face)?;
                let ty = self.force(ty, face)?;
                if let Val::Sigma(a, b) = self.get(ty) {
                    if matches!(self.get(v), Val::Fst(_)) {
                        Ok(a)
                    } else {
                        let p = self.fst(p);
                        Ok(self.inst(&b, p))
                    }
                } else {
                    Err(Error::plain("internal error: neutral pair type"))
                }
            }
            Val::If(p, _, _, c) | Val::NatElim(p, _, _, c) => Ok(self.app(p, c)),
            Val::PApp(p, d) => {
                let ty = self.neutral_type(p, face)?;
                let ty = self.force(ty, face)?;
                if let Val::Path(b, _, _) = self.get(ty) {
                    Ok(self.inst_dim(&b, d))
                } else {
                    Err(Error::plain("internal error: neutral path type"))
                }
            }
            Val::Com(c) => Ok(self.restrict(c.family, c.dim, c.to)),
            Val::System(ty, _) => Ok(ty),
            Val::Unglue(g, _) => {
                let g = self.force_glue(g, face)?;
                if let Val::Glue(base, _) = self.get(g) {
                    Ok(base)
                } else {
                    Err(Error::plain("internal error: unglue type"))
                }
            }
            Val::Susp(_, _) | Val::Sub(_, _) => {
                let w = self.force(v, face)?;
                self.neutral_type(w, face)
            }
            _ => Err(Error::plain(format!(
                "internal error: missing neutral type for {:?}",
                self.get(v)
            ))),
        }
    }
    fn reduce_com(&mut self, c: Composition, face: FaceId) -> Result<Option<ValId>> {
        if self.faces.equal(face, c.from, c.to)? {
            return Ok(Some(c.cap));
        }
        for &(f, v) in &c.tubes {
            if self.faces.entails(face, f)? {
                return Ok(Some(self.restrict(v, c.dim, c.to)));
            }
        }
        let family = self.force(c.family, face)?;
        match self.get(family) {
            Val::Bool | Val::Nat => {
                let cap = self.force(c.cap, face)?;
                let tag = match self.get(cap) {
                    Val::True => 0,
                    Val::False => 1,
                    Val::Zero => 2,
                    Val::Suc(_) => 3,
                    _ => return Ok(None),
                };
                let mut ts = vec![];
                for (f, t) in c.tubes {
                    let under = self.faces.and(face, f);
                    if self.faces.inconsistent(under)? {
                        continue;
                    }
                    let t = self.force(t, under)?;
                    match (tag, self.get(t)) {
                        (0, Val::True) | (1, Val::False) | (2, Val::Zero) => {}
                        (3, Val::Suc(n)) => ts.push((f, n)),
                        _ => return Ok(None),
                    }
                }
                if let Val::Suc(n) = self.get(cap) {
                    let n = self.alloc(Val::Com(Composition {
                        cap: n,
                        tubes: ts,
                        ..c
                    }));
                    Ok(Some(self.alloc(Val::Suc(n))))
                } else {
                    Ok(Some(cap))
                }
            }
            Val::Sigma(a, b) => {
                let cap_a = self.fst(c.cap);
                let tubes_a = c
                    .tubes
                    .iter()
                    .map(|(f, v)| (*f, self.fst(*v)))
                    .collect::<Vec<_>>();
                let first = self.alloc(Val::Com(Composition {
                    family: a,
                    cap: cap_a,
                    tubes: tubes_a.clone(),
                    ..c.clone()
                }));
                let y = self.fresh_dim();
                let filler = self.alloc(Val::Com(Composition {
                    family: a,
                    to: Dim::Var(y),
                    cap: cap_a,
                    tubes: tubes_a,
                    ..c.clone()
                }));
                let cod = self.inst(&b, filler);
                let cod = self.restrict(cod, c.dim, Dim::Var(y));
                let cap = self.snd(c.cap);
                let tubes = c
                    .tubes
                    .iter()
                    .map(|(f, v)| {
                        let t = self.snd(*v);
                        (*f, self.restrict(t, c.dim, Dim::Var(y)))
                    })
                    .collect();
                let second = self.alloc(Val::Com(Composition {
                    dim: y,
                    family: cod,
                    cap,
                    tubes,
                    ..c
                }));
                Ok(Some(self.alloc(Val::Pair(first, second))))
            }
            Val::Pi(a, b) => {
                let y = self.fresh_dim();
                let x = self.fresh_term();
                let target_a = self.restrict(a, c.dim, c.to);
                let arg = self.alloc(Val::Var(x, Some(target_a)));
                let filler = self.alloc(Val::Com(Composition {
                    dim: c.dim,
                    family: a,
                    from: c.to,
                    to: Dim::Var(y),
                    cap: arg,
                    tubes: vec![],
                }));
                let back = self.restrict(filler, y, c.from);
                let cap = self.app(c.cap, back);
                let cod = self.inst(&b, filler);
                let cod = self.restrict(cod, c.dim, Dim::Var(y));
                let tubes = c
                    .tubes
                    .iter()
                    .map(|(f, v)| {
                        let t = self.restrict(*v, c.dim, Dim::Var(y));
                        (*f, self.app(t, filler))
                    })
                    .collect();
                let body = self.alloc(Val::Com(Composition {
                    dim: y,
                    family: cod,
                    cap,
                    tubes,
                    ..c
                }));
                Ok(Some(self.alloc(Val::Lam(Binder { var: x, body }))))
            }
            Val::Path(b, l, r) => {
                let x = self.fresh_dim();
                let d = Dim::Var(x);
                let a = self.inst_dim(&b, d);
                let cap = self.at(c.cap, d);
                let mut tubes = c
                    .tubes
                    .iter()
                    .map(|(f, v)| (*f, self.at(*v, d)))
                    .collect::<Vec<_>>();
                tubes.push((self.faces.eq(d, Dim::Zero), l));
                tubes.push((self.faces.eq(d, Dim::One), r));
                let body = self.alloc(Val::Com(Composition {
                    family: a,
                    cap,
                    tubes,
                    ..c
                }));
                Ok(Some(self.alloc(Val::PLam(Binder { var: x, body }))))
            }
            Val::Glue(base, branches) => Ok(Some(self.compose_glue(c, base, branches)?)),
            Val::U(_) => Ok(Some(self.compose_universe(c))),
            _ => Ok(None),
        }
    }
    pub fn optimized_quote(&self) -> bool {
        self.optimized
    }
    pub fn profile_snapshot(&self, bytes: usize) {
        if let Some(p) = &self.profile {
            let mut kinds = std::collections::BTreeMap::new();
            for i in 0..self.values.len() {
                let kind = match self.values.get(ValId::new(i)) {
                    Val::Sub(..) => "Sub",
                    Val::Susp(..) => "Susp",
                    Val::Var(..) => "Var",
                    Val::Com(..) => "Com",
                    Val::Lam(..) | Val::Pi(..) | Val::Sigma(..) | Val::Path(..) | Val::PLam(..) => {
                        "Binder"
                    }
                    _ => "Other",
                };
                *kinds.entry(kind).or_insert(0usize) += 1;
            }
            let mut sites: Vec<_> = p.sites.iter().collect();
            sites.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
            sites.truncate(10);
            let mut terms: Vec<_> = p.unfolds.iter().collect();
            terms.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
            terms.truncate(10);
            eprintln!(
                "PROFILE bytes={bytes} steps={} values={} envs={} subs={} faces={} pushes={} collections={} reclaimed={} allocated_values={} kinds={kinds:?} sites={sites:?} source_offsets={terms:?}",
                self.steps,
                self.values.len(),
                self.envs.len(),
                self.subs.len(),
                self.faces.len(),
                p.pushes,
                self.collections,
                self.reclaimed_nodes,
                self.allocated_values
            );
        }
    }
    pub fn statistics(&self) -> Statistics {
        let payload = self.envs_payload() + self.values_payload() + self.subs_payload();
        Statistics {
            steps: self.steps,
            value_nodes: self.values.len(),
            environment_nodes: self.envs.len(),
            substitution_nodes: self.subs.len(),
            face_nodes: self.faces.len(),
            arena_bytes: self.values.bytes()
                + self.envs.bytes()
                + self.subs.bytes()
                + self.faces.bytes()
                + payload,
            cache_entries: self.cache.len(),
            allocated_values: self.allocated_values,
            collections: self.collections,
            reclaimed_nodes: self.reclaimed_nodes,
        }
    }
    fn envs_payload(&self) -> usize {
        (0..self.envs.len())
            .map(|i| {
                let e = self.envs.get(EnvId::new(i));
                e.terms.capacity() * size_of::<ValId>() + e.dims.capacity() * size_of::<Dim>()
            })
            .sum()
    }
    fn subs_payload(&self) -> usize {
        (0..self.subs.len())
            .map(|i| {
                let s = self.subs.get(SubId::new(i));
                s.terms.capacity() * size_of::<(u32, ValId)>()
                    + s.dims.capacity() * size_of::<(u32, Dim)>()
            })
            .sum()
    }
    fn values_payload(&self) -> usize {
        (0..self.values.len())
            .map(|i| match self.values.get(ValId::new(i)) {
                Val::Com(c) => c.tubes.capacity() * size_of::<(FaceId, ValId)>(),
                Val::System(_, bs) | Val::GlueIntro(_, bs) => {
                    bs.capacity() * size_of::<(FaceId, ValId)>()
                }
                Val::Glue(_, bs) => bs.capacity() * size_of::<(FaceId, ValId, ValId)>(),
                _ => 0,
            })
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn substitutions_compose_and_unblock_paths() {
        for optimized in [false, true] {
            let program = Program::default();
            let mut e = Engine::new(&program, optimized, 100_000, 100_000);
            let face = e.faces.top();
            let bool_ty = e.alloc(Val::Bool);
            let t = e.alloc(Val::True);
            let f = e.alloc(Val::False);
            let k = e.fresh_dim();
            let path_ty = e.alloc(Val::Path(
                Binder {
                    var: k,
                    body: bool_ty,
                },
                t,
                f,
            ));
            let p = e.variable(path_ty);
            let i = e.fresh_dim();
            let j = e.fresh_dim();
            let open = e.at(p, Dim::Var(i));
            let identity = e.restrict(open, i, Dim::Var(i));
            assert_eq!(identity, open);
            for (endpoint, expected) in [(Dim::Zero, t), (Dim::One, f)] {
                let first = e.restrict(open, i, Dim::Var(j));
                let composed = e.restrict(first, j, endpoint);
                let direct = e.restrict(open, i, endpoint);
                assert!(e.conv(composed, direct, Some(bool_ty), face).unwrap());
                assert_eq!(e.force(composed, face).unwrap(), expected);
            }
            let at_zero = e.faces.eq(Dim::Var(i), Dim::Zero);
            let at_one = e.faces.eq(Dim::Var(i), Dim::One);
            assert_eq!(e.force(open, at_zero).unwrap(), t);
            assert_eq!(e.force(open, at_one).unwrap(), f);
            let open = e.force(open, face).unwrap();
            assert!(matches!(e.get(open), Val::PApp(..)));
        }
    }

    #[test]
    fn native_singleton_filler_agrees_with_checked_library() {
        let source = format!(
            "{}\n(def test-type (U 0) Nat)\n(def test-equiv (app (app Equiv Nat) Nat) (app id-equiv Nat))",
            include_str!("../examples/prelude.kamo")
        );
        let checked = crate::CheckedProgram::check(&source).unwrap();
        let p = &checked.program;
        let mut e = Engine::new(p, true, 1_000_000, 250_000);
        let env = e.env(Env::default());
        let face = e.faces.top();
        let nat = e.alloc(Val::Nat);
        let derived = e.identity_equiv(nat);
        let library = e.thunk(p.decls.last().unwrap().body, env);
        let ty = e.equiv_type(nat, nat);
        assert!(e.conv(derived, library, Some(ty), face).unwrap());
    }
}

#[cfg(test)]
mod substitution_face_regression {
    use super::*;
    #[test]
    fn reference_shared_substitution() {
        check(false);
    }
    #[test]
    fn optimized_shared_substitution() {
        check(true);
    }
    fn check(optimized: bool) {
        {
            let program = Program::default();
            let mut e = Engine::new(&program, optimized, 100_000, 100_000);
            let u = e.alloc(Val::U(0));
            let bool_ty = e.alloc(Val::Bool);
            let k = e.fresh_dim();
            let pt = e.alloc(Val::Path(Binder { var: k, body: u }, bool_ty, bool_ty));
            let p = e.variable(pt);
            let i = e.fresh_dim();
            let j = e.fresh_dim();
            let face = e.faces.eq(Dim::Var(i), Dim::Var(j));
            let a = e.at(p, Dim::Var(i));
            let b = e.at(p, Dim::Var(j));
            let s = e.substitution(Sub {
                terms: vec![],
                dims: vec![(i, Dim::Zero)],
                compose: None,
            });
            let a = e.sub(a, s);
            let b = e.sub(b, s);
            let lazy = e.conv(a, b, Some(u), face).unwrap();
            let aa = e.force(a, face).unwrap();
            let bb = e.force(b, face).unwrap();
            let forced = e.conv(aa, bb, Some(u), face).unwrap();
            assert!(!lazy, "the substituted terms must not compare equal");
            assert_eq!(lazy, forced, "conversion changed after forcing");
        }
    }
}

#[path = "collect.rs"]
mod collect;

#[path = "support.rs"]
mod support;
