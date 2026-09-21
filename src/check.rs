use crate::eval::{Binder, Engine, Env, EnvId, Val, ValId};
use crate::face::{Dim, FaceId};
use crate::syntax::{Term, TermId};
use crate::{Error, Result};

#[derive(Clone)]
struct Context {
    env: EnvId,
    types: Vec<ValId>,
    face: FaceId,
}
impl Engine<'_> {
    pub fn check_declaration(&mut self, index: usize) -> Result<()> {
        let decl = &self.program.decls[index];
        {
            if std::env::var_os("KAMO_TRACE_CHECK").is_some() {
                eprintln!("checking {} ({} steps)", decl.name, self.steps);
            }
            let env = self.env(Env::default());
            let face = self.faces.top();
            let ctx = Context {
                env,
                types: vec![],
                face,
            };
            self.sort(decl.ty, &ctx).map_err(|mut e| {
                e.message = format!("checking type of {}: {}", decl.name, e.message);
                e
            })?;
            let ty = self.thunk(decl.ty, env);
            self.check(decl.body, ty, &ctx).map_err(|mut e| {
                e.message = format!("checking {}: {}", decl.name, e.message);
                e
            })?;
        }
        self.tick()?;
        Ok(())
    }
    fn error(&self, t: TermId, message: impl Into<String>) -> Error {
        Error::at(self.program.terms.get(t).offset, message)
    }
    fn extend(&mut self, ctx: &Context, ty: ValId) -> (Context, ValId) {
        let x = self.variable(ty);
        let mut env = self.environment(ctx.env);
        env.terms.push(x);
        let mut c = ctx.clone();
        c.env = self.env(env);
        c.types.push(ty);
        (c, x)
    }
    fn interval(&mut self, ctx: &Context) -> (Context, u32) {
        let i = self.fresh_dim();
        let mut env = self.environment(ctx.env);
        env.dims.push(Dim::Var(i));
        let mut c = ctx.clone();
        c.env = self.env(env);
        (c, i)
    }
    fn interval_at(&mut self, ctx: &Context, d: Dim) -> Context {
        let mut env = self.environment(ctx.env);
        env.dims.push(d);
        Context {
            env: self.env(env),
            ..ctx.clone()
        }
    }
    fn sort(&mut self, t: TermId, ctx: &Context) -> Result<u32> {
        let ty = self.infer(t, ctx)?;
        let ty = self.force(ty, ctx.face)?;
        if let Val::U(l) = self.get(ty) {
            Ok(l)
        } else {
            Err(self.error(t, "expected a type (an inhabitant of a universe)"))
        }
    }
    fn check(&mut self, t: TermId, ty: ValId, ctx: &Context) -> Result<()> {
        self.check_inner(t, ty, ctx).map_err(|mut e| {
            if e.offset.is_none() {
                e.offset = Some(self.program.terms.get(t).offset);
            }
            e
        })
    }
    fn check_inner(&mut self, t: TermId, ty: ValId, ctx: &Context) -> Result<()> {
        self.tick()?;
        if self.faces.inconsistent(ctx.face)? {
            return Ok(());
        }
        // Equality and checking are local on covers; no branch choice is global.
        let clauses = self.faces.clauses(ctx.face)?;
        if clauses.len() > 1 {
            for face in clauses {
                self.check(
                    t,
                    ty,
                    &Context {
                        face,
                        ..ctx.clone()
                    },
                )?;
            }
            return Ok(());
        }
        let ty = self.force(ty, ctx.face)?;
        match (self.program.terms.get(t).term.clone(), self.get(ty)) {
            (Term::Lam(body), Val::Pi(a, b)) => {
                let (ctx, x) = self.extend(ctx, a);
                let b = self.inst(&b, x);
                self.check(body, b, &ctx)
            }
            (Term::Pair(a, b), Val::Sigma(first, second)) => {
                self.check(a, first, ctx)?;
                let a = self.thunk(a, ctx.env);
                let second = self.inst(&second, a);
                self.check(b, second, ctx)
            }
            (Term::PLam(body), Val::Path(family, left, right)) => {
                let (inner, i) = self.interval(ctx);
                let a = self.inst_dim(&family, Dim::Var(i));
                self.check(body, a, &inner)?;
                for (d, endpoint) in [(Dim::Zero, left), (Dim::One, right)] {
                    let at = self.interval_at(ctx, d);
                    let body = self.thunk(body, at.env);
                    let a = self.inst_dim(&family, d);
                    if !self.conv(body, endpoint, Some(a), ctx.face)? {
                        return Err(
                            self.error(t, "path endpoint does not match its declared boundary")
                        );
                    }
                }
                Ok(())
            }
            _ => {
                let got = self.infer(t, ctx)?;
                if self.conv(got, ty, None, ctx.face)? {
                    Ok(())
                } else {
                    Err(self.error(
                        t,
                        "type mismatch (universe levels are explicit and non-cumulative)",
                    ))
                }
            }
        }
    }
    fn infer(&mut self, t: TermId, ctx: &Context) -> Result<ValId> {
        self.tick()?;
        let ty = match self.program.terms.get(t).term.clone() {
            Term::Var(i) => return Ok(ctx.types[ctx.types.len() - 1 - i]),
            Term::Global(i) => {
                let e = self.env(Env::default());
                return Ok(self.thunk(self.program.decls[i].ty, e));
            }
            Term::U(l) => Val::U(
                l.checked_add(1)
                    .ok_or_else(|| self.error(t, "universe level overflow"))?,
            ),
            Term::Bool | Term::Nat => Val::U(0),
            Term::True | Term::False => Val::Bool,
            Term::Zero => Val::Nat,
            Term::Suc(n) => {
                let nat = self.alloc(Val::Nat);
                self.check(n, nat, ctx)?;
                Val::Nat
            }
            Term::Pi(a, b) | Term::Sigma(a, b) => {
                let l = self.sort(a, ctx)?;
                let a = self.thunk(a, ctx.env);
                let (inner, _) = self.extend(ctx, a);
                let m = self.sort(b, &inner)?;
                Val::U(l.max(m))
            }
            Term::Ann(body, ty) => {
                self.sort(ty, ctx)?;
                let ty = self.thunk(ty, ctx.env);
                self.check(body, ty, ctx)?;
                return Ok(ty);
            }
            Term::App(f, a) => {
                let ty = self.infer(f, ctx)?;
                let ty = self.force(ty, ctx.face)?;
                if let Val::Pi(dom, cod) = self.get(ty) {
                    self.check(a, dom, ctx)?;
                    let a = self.thunk(a, ctx.env);
                    return Ok(self.inst(&cod, a));
                }
                return Err(self.error(t, "application expects a dependent function"));
            }
            Term::Fst(p) | Term::Snd(p) => {
                let ty = self.infer(p, ctx)?;
                let ty = self.force(ty, ctx.face)?;
                if let Val::Sigma(a, b) = self.get(ty) {
                    if matches!(self.program.terms.get(t).term, Term::Fst(_)) {
                        return Ok(a);
                    }
                    let p = self.thunk(p, ctx.env);
                    let a = self.fst(p);
                    return Ok(self.inst(&b, a));
                }
                return Err(self.error(t, "projection expects a dependent pair"));
            }
            Term::If(p, a, b, c) => {
                let bool_ty = self.alloc(Val::Bool);
                self.check(c, bool_ty, ctx)?;
                self.check_motive(p, bool_ty, ctx)?;
                let p = self.thunk(p, ctx.env);
                let tv = self.alloc(Val::True);
                let fv = self.alloc(Val::False);
                let ta = self.app(p, tv);
                let tb = self.app(p, fv);
                self.check(a, ta, ctx)?;
                self.check(b, tb, ctx)?;
                let c = self.thunk(c, ctx.env);
                return Ok(self.app(p, c));
            }
            Term::NatElim(p, z, s, n) => {
                let nat = self.alloc(Val::Nat);
                self.check(n, nat, ctx)?;
                self.check_motive(p, nat, ctx)?;
                let p = self.thunk(p, ctx.env);
                let zero = self.alloc(Val::Zero);
                let base = self.app(p, zero);
                self.check(z, base, ctx)?;
                let x = self.fresh_term();
                let xv = self.alloc(Val::Var(x, Some(nat)));
                let px = self.app(p, xv);
                let sx = self.alloc(Val::Suc(xv));
                let result = self.app(p, sx);
                let ih = self.fresh_term();
                let step = self.alloc(Val::Pi(
                    px,
                    Binder {
                        var: ih,
                        body: result,
                    },
                ));
                let step = self.alloc(Val::Pi(nat, Binder { var: x, body: step }));
                self.check(s, step, ctx)?;
                let n = self.thunk(n, ctx.env);
                return Ok(self.app(p, n));
            }
            Term::Path(a, l, r) => {
                let (inner, _) = self.interval(ctx);
                let level = self.sort(a, &inner)?;
                for (d, v) in [(Dim::Zero, l), (Dim::One, r)] {
                    let at = self.interval_at(ctx, d);
                    let a = self.thunk(a, at.env);
                    self.check(v, a, ctx)?;
                }
                Val::U(level)
            }
            Term::PApp(p, d) => {
                let ty = self.infer(p, ctx)?;
                let ty = self.force(ty, ctx.face)?;
                if let Val::Path(b, _, _) = self.get(ty) {
                    return Ok(self.inst_dim(&b, self.dim(d, ctx.env)));
                }
                return Err(self.error(t, "'at' expects a path"));
            }
            Term::Com {
                family,
                from,
                to,
                cap,
                tubes,
            } => {
                let (inner, _) = self.interval(ctx);
                self.sort(family, &inner)?;
                let from = self.dim(from, ctx.env);
                let to = self.dim(to, ctx.env);
                let source = self.interval_at(ctx, from);
                let source_ty = self.thunk(family, source.env);
                self.check(cap, source_ty, ctx)?;
                let cap = self.thunk(cap, ctx.env);
                let mut previous = vec![];
                for (f, tube) in tubes {
                    let f = self.face(&f, ctx.env);
                    let under = self.faces.and(ctx.face, f);
                    let branch = Context {
                        face: under,
                        ..inner.clone()
                    };
                    let ty = self.thunk(family, inner.env);
                    self.check(tube, ty, &branch)?;
                    let start = self.thunk(tube, source.env);
                    if !self.conv(start, cap, Some(source_ty), under)? {
                        return Err(self.error(
                            tube,
                            "composition tube disagrees with its cap at the source",
                        ));
                    }
                    let v = self.thunk(tube, inner.env);
                    for &(old_face, old_v) in &previous {
                        let overlap = self.faces.and(under, old_face);
                        if !self.conv(v, old_v, Some(ty), overlap)? {
                            return Err(
                                self.error(tube, "composition tubes disagree on an overlap")
                            );
                        }
                    }
                    previous.push((f, v));
                }
                let target = self.interval_at(ctx, to);
                return Ok(self.thunk(family, target.env));
            }
            Term::System(a, branches) => {
                self.sort(a, ctx)?;
                let a = self.thunk(a, ctx.env);
                let mut cover = self.faces.bot();
                let mut previous = vec![];
                for (f, body) in branches {
                    let f = self.face(&f, ctx.env);
                    cover = self.faces.or(cover, f);
                    let under = self.faces.and(ctx.face, f);
                    self.check(
                        body,
                        a,
                        &Context {
                            face: under,
                            ..ctx.clone()
                        },
                    )?;
                    let v = self.thunk(body, ctx.env);
                    for &(old_face, old_v) in &previous {
                        let overlap = self.faces.and(under, old_face);
                        if !self.conv(v, old_v, Some(a), overlap)? {
                            return Err(self.error(body, "system branches disagree on an overlap"));
                        }
                    }
                    previous.push((f, v));
                }
                if !self.faces.entails(ctx.face, cover)? {
                    return Err(self.error(t, "system faces do not cover the current face context"));
                }
                return Ok(a);
            }
            Term::Glue(base, branches) => {
                let level = self.sort(base, ctx)?;
                let base = self.thunk(base, ctx.env);
                let universe = self.alloc(Val::U(level));
                let mut previous = vec![];
                for (f, a, e) in branches {
                    let f = self.face(&f, ctx.env);
                    let under = self.faces.and(ctx.face, f);
                    let branch = Context {
                        face: under,
                        ..ctx.clone()
                    };
                    self.check(a, universe, &branch)?;
                    let a = self.thunk(a, ctx.env);
                    let eqty = self.equiv_type(a, base);
                    self.check(e, eqty, &branch)?;
                    let e = self.thunk(e, ctx.env);
                    for &(g, b, q) in &previous {
                        let overlap = self.faces.and(under, g);
                        if !self.conv(a, b, None, overlap)?
                            || !self.conv(e, q, Some(eqty), overlap)?
                        {
                            return Err(self.error(t, "Glue data disagree on an overlap"));
                        }
                    }
                    previous.push((f, a, e));
                }
                Val::U(level)
            }
            Term::Unglue(g, v) => {
                self.sort(g, ctx)?;
                let g = self.thunk(g, ctx.env);
                let raw = self.force_glue(g, ctx.face)?;
                if let Val::Glue(base, _) = self.get(raw) {
                    self.check(v, g, ctx)?;
                    return Ok(base);
                }
                return Err(self.error(t, "unglue requires an explicit Glue type"));
            }
            Term::GlueIntro(g, base, branches) => {
                self.sort(g, ctx)?;
                let g = self.thunk(g, ctx.env);
                let raw = self.force_glue(g, ctx.face)?;
                let Val::Glue(base_ty, data) = self.get(raw) else {
                    return Err(self.error(t, "glue requires an explicit Glue type"));
                };
                self.check(base, base_ty, ctx)?;
                let base = self.thunk(base, ctx.env);
                let mut domain = self.faces.bot();
                for (f, _, _) in &data {
                    domain = self.faces.or(domain, *f);
                }
                let mut cover = self.faces.bot();
                let mut tops = vec![];
                for (f, body) in branches {
                    let f = self.face(&f, ctx.env);
                    let under = self.faces.and(ctx.face, f);
                    if !self.faces.entails(under, domain)? {
                        return Err(
                            self.error(body, "glue element face exceeds the Glue type's domain")
                        );
                    }
                    cover = self.faces.or(cover, f);
                    let v = self.thunk(body, ctx.env);
                    for &(h, a, e) in &data {
                        let overlap = self.faces.and(under, h);
                        self.check(
                            body,
                            a,
                            &Context {
                                face: overlap,
                                ..ctx.clone()
                            },
                        )?;
                        let fun = self.fst(e);
                        let image = self.app(fun, v);
                        if !self.conv(image, base, Some(base_ty), overlap)? {
                            return Err(
                                self.error(body, "glue element image disagrees with its base")
                            );
                        }
                        for &(old_face, old_v) in &tops {
                            let both = self.faces.and(overlap, old_face);
                            if !self.conv(v, old_v, Some(a), both)? {
                                return Err(
                                    self.error(body, "glue elements disagree on an overlap")
                                );
                            }
                        }
                    }
                    tops.push((f, v));
                }
                let required = self.faces.and(ctx.face, domain);
                if !self.faces.entails(required, cover)? {
                    return Err(self.error(t, "glue elements do not cover the Glue type's domain"));
                }
                return Ok(g);
            }
            Term::Lam(_) | Term::Pair(_, _) | Term::PLam(_) => {
                return Err(self.error(t, "cannot infer an introduction form; add (ann term type)"));
            }
        };
        Ok(self.alloc(ty))
    }
    fn check_motive(&mut self, p: TermId, domain: ValId, ctx: &Context) -> Result<()> {
        // A syntactic lambda is permitted here without a universe annotation.
        if let Term::Lam(body) = self.program.terms.get(p).term {
            let (inner, _) = self.extend(ctx, domain);
            self.sort(body, &inner)?;
            return Ok(());
        }
        let ty = self.infer(p, ctx)?;
        let ty = self.force(ty, ctx.face)?;
        if let Val::Pi(a, b) = self.get(ty)
            && self.conv(a, domain, None, ctx.face)?
        {
            let x = self.variable(a);
            let b = self.inst(&b, x);
            let b = self.force(b, ctx.face)?;
            if matches!(self.get(b), Val::U(_)) {
                return Ok(());
            }
        }
        Err(self.error(
            p,
            "eliminator motive must map its argument type to a universe",
        ))
    }
    /// Type-directed eta equality; term identities are only compared in one face context.
    pub fn conv(&mut self, a: ValId, b: ValId, ty: Option<ValId>, face: FaceId) -> Result<bool> {
        self.tick()?;
        if self.faces.inconsistent(face)? {
            return Ok(true);
        }
        if a == b {
            return Ok(true);
        }
        if self.same(a, b, face, 128)? {
            return Ok(true);
        }
        let clauses = self.faces.clauses(face)?;
        if clauses.len() > 1 {
            for f in clauses {
                if !self.conv(a, b, ty, f)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        if let Some(ty) = ty {
            let ty = self.force(ty, face)?;
            match self.get(ty) {
                Val::Pi(dom, cod) => {
                    let x = self.variable(dom);
                    let ax = self.app(a, x);
                    let bx = self.app(b, x);
                    let cod = self.inst(&cod, x);
                    return self.conv(ax, bx, Some(cod), face);
                }
                Val::Sigma(dom, cod) => {
                    let ax = self.fst(a);
                    let bx = self.fst(b);
                    if !self.conv(ax, bx, Some(dom), face)? {
                        return Ok(false);
                    }
                    let cod = self.inst(&cod, ax);
                    let ay = self.snd(a);
                    let by = self.snd(b);
                    return self.conv(ay, by, Some(cod), face);
                }
                Val::Path(family, _, _) => {
                    let i = self.fresh_dim();
                    let d = Dim::Var(i);
                    let ax = self.at(a, d);
                    let bx = self.at(b, d);
                    let cod = self.inst_dim(&family, d);
                    return self.conv(ax, bx, Some(cod), face);
                }
                Val::Glue(base, branches) => {
                    let ax = self.alloc(Val::Unglue(ty, a));
                    let bx = self.alloc(Val::Unglue(ty, b));
                    if !self.conv(ax, bx, Some(base), face)? {
                        return Ok(false);
                    }
                    for (f, t, _) in branches {
                        let under = self.faces.and(face, f);
                        if !self.conv(a, b, Some(t), under)? {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
                _ => {}
            }
        }
        let a = self.force(a, face)?;
        let b = self.force(b, face)?;
        if a == b {
            return Ok(true);
        }
        if let Val::System(_, branches) = self.get(a) {
            for (f, v) in branches {
                let under = self.faces.and(face, f);
                if !self.conv(v, b, ty, under)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        if let Val::System(_, branches) = self.get(b) {
            for (f, v) in branches {
                let under = self.faces.and(face, f);
                if !self.conv(a, v, ty, under)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        match (self.get(a), self.get(b)) {
            (Val::U(a), Val::U(b)) => Ok(a == b),
            (Val::Bool, Val::Bool)
            | (Val::Nat, Val::Nat)
            | (Val::True, Val::True)
            | (Val::False, Val::False)
            | (Val::Zero, Val::Zero) => Ok(true),
            (Val::Var(a, _), Val::Var(b, _)) => Ok(a == b),
            (Val::Pi(a, x), Val::Pi(b, y)) | (Val::Sigma(a, x), Val::Sigma(b, y)) => {
                if !self.conv(a, b, None, face)? {
                    return Ok(false);
                }
                let v = self.variable(a);
                let x = self.inst(&x, v);
                let y = self.inst(&y, v);
                self.conv(x, y, None, face)
            }
            (Val::Path(x, l, r), Val::Path(y, m, n)) => {
                let i = self.fresh_dim();
                let x_body = self.inst_dim(&x, Dim::Var(i));
                let y_body = self.inst_dim(&y, Dim::Var(i));
                if !self.conv(x_body, y_body, None, face)? {
                    return Ok(false);
                }
                let a = self.inst_dim(&x, Dim::Zero);
                let b = self.inst_dim(&x, Dim::One);
                Ok(self.conv(l, m, Some(a), face)? && self.conv(r, n, Some(b), face)?)
            }
            (Val::Suc(a), Val::Suc(b)) => {
                let ty = self.alloc(Val::Nat);
                self.conv(a, b, Some(ty), face)
            }
            (Val::App(f, a), Val::App(g, b)) => {
                if !self.conv(f, g, None, face)? {
                    return Ok(false);
                }
                let ft = self.neutral_type(f, face)?;
                let ft = self.force(ft, face)?;
                let ty = if let Val::Pi(a, _) = self.get(ft) {
                    Some(a)
                } else {
                    None
                };
                self.conv(a, b, ty, face)
            }
            (Val::Fst(a), Val::Fst(b)) | (Val::Snd(a), Val::Snd(b)) => self.conv(a, b, None, face),
            (Val::PApp(a, i), Val::PApp(b, j)) => {
                Ok(self.faces.equal(face, i, j)? && self.conv(a, b, None, face)?)
            }
            (Val::If(p, a, b, c), Val::If(q, d, e, f)) => {
                let bool_ty = self.alloc(Val::Bool);
                let x = self.fresh_term();
                let u = self.alloc(Val::U(0));
                let motive = self.alloc(Val::Pi(bool_ty, Binder { var: x, body: u }));
                // Motive universes need not be U0; function eta only needs the domain here.
                if !self.conv(p, q, Some(motive), face)? || !self.conv(c, f, Some(bool_ty), face)? {
                    return Ok(false);
                }
                let tv = self.alloc(Val::True);
                let fv = self.alloc(Val::False);
                let ta = self.app(p, tv);
                let tb = self.app(p, fv);
                Ok(self.conv(a, d, Some(ta), face)? && self.conv(b, e, Some(tb), face)?)
            }
            (Val::NatElim(p, z, s, n), Val::NatElim(q, w, t, m)) => {
                let nat = self.alloc(Val::Nat);
                let x = self.variable(nat);
                let px = self.app(p, x);
                let qx = self.app(q, x);
                if !self.conv(px, qx, None, face)? || !self.conv(n, m, Some(nat), face)? {
                    return Ok(false);
                }
                let zero = self.alloc(Val::Zero);
                let pz = self.app(p, zero);
                if !self.conv(z, w, Some(pz), face)? {
                    return Ok(false);
                }
                let ih = self.variable(px);
                let sx = self.app(s, x);
                let tx = self.app(t, x);
                let sx = self.app(sx, ih);
                let tx = self.app(tx, ih);
                let next = self.alloc(Val::Suc(x));
                let pn = self.app(p, next);
                self.conv(sx, tx, Some(pn), face)
            }
            (Val::Com(a), Val::Com(b)) => {
                if !self.faces.equal(face, a.from, b.from)?
                    || !self.faces.equal(face, a.to, b.to)?
                {
                    return Ok(false);
                }
                let i = self.fresh_dim();
                let d = Dim::Var(i);
                let af = self.restrict(a.family, a.dim, d);
                let bf = self.restrict(b.family, b.dim, d);
                if !self.conv(af, bf, None, face)? {
                    return Ok(false);
                }
                let src = self.restrict(a.family, a.dim, a.from);
                if !self.conv(a.cap, b.cap, Some(src), face)? {
                    return Ok(false);
                }
                let mut ac = self.faces.bot();
                let mut bc = self.faces.bot();
                for (f, _) in &a.tubes {
                    ac = self.faces.or(ac, *f);
                }
                for (f, _) in &b.tubes {
                    bc = self.faces.or(bc, *f);
                }
                let ac = self.faces.and(face, ac);
                let bc = self.faces.and(face, bc);
                if !self.faces.entails(ac, bc)? || !self.faces.entails(bc, ac)? {
                    return Ok(false);
                }
                for (f, x) in a.tubes {
                    for &(g, y) in &b.tubes {
                        let overlap = self.faces.and(f, g);
                        let overlap = self.faces.and(face, overlap);
                        let x = self.restrict(x, a.dim, d);
                        let y = self.restrict(y, b.dim, d);
                        if !self.conv(x, y, Some(af), overlap)? {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
            (Val::Glue(a, bs), Val::Glue(b, cs)) => {
                if !self.conv(a, b, None, face)? {
                    return Ok(false);
                }
                let mut ac = self.faces.bot();
                let mut bc = self.faces.bot();
                for (f, _, _) in &bs {
                    ac = self.faces.or(ac, *f);
                }
                for (f, _, _) in &cs {
                    bc = self.faces.or(bc, *f);
                }
                let ac = self.faces.and(face, ac);
                let bc = self.faces.and(face, bc);
                if !self.faces.entails(ac, bc)? || !self.faces.entails(bc, ac)? {
                    return Ok(false);
                }
                for (f, t, e) in bs {
                    for &(g, u, q) in &cs {
                        let overlap = self.faces.and(f, g);
                        let overlap = self.faces.and(face, overlap);
                        let eqty = self.equiv_type(t, a);
                        if !self.conv(t, u, None, overlap)?
                            || !self.conv(e, q, Some(eqty), overlap)?
                        {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
            (Val::Unglue(g, x), Val::Unglue(h, y)) => {
                Ok(self.conv(g, h, None, face)? && self.conv(x, y, None, face)?)
            }
            _ => Ok(false),
        }
    }
}
