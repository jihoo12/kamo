//! Semantic expansions of ABCFHL §§2.7, 2.11, 2.12. No univalence constant.
use crate::Result;
use crate::eval::{Binder, Composition, Engine, Val, ValId};
use crate::face::{Dim, FaceId};

impl Engine<'_> {
    pub fn fiber(&mut self, a: ValId, b: ValId, f: ValId, y: ValId) -> ValId {
        let x = self.fresh_term();
        let xv = self.alloc(Val::Var(x, Some(a)));
        let fx = self.app(f, xv);
        let i = self.fresh_dim();
        let path = self.alloc(Val::Path(Binder { var: i, body: b }, fx, y));
        self.alloc(Val::Sigma(a, Binder { var: x, body: path }))
    }
    pub fn contractible(&mut self, a: ValId) -> ValId {
        let x = self.fresh_term();
        let xv = self.alloc(Val::Var(x, Some(a)));
        let y = self.fresh_term();
        let yv = self.alloc(Val::Var(y, Some(a)));
        let i = self.fresh_dim();
        let p = self.alloc(Val::Path(Binder { var: i, body: a }, xv, yv));
        let all = self.alloc(Val::Pi(a, Binder { var: y, body: p }));
        self.alloc(Val::Sigma(a, Binder { var: x, body: all }))
    }
    pub fn is_equiv(&mut self, a: ValId, b: ValId, f: ValId) -> ValId {
        let y = self.fresh_term();
        let yv = self.alloc(Val::Var(y, Some(b)));
        let fiber = self.fiber(a, b, f, yv);
        let contr = self.contractible(fiber);
        self.alloc(Val::Pi(
            b,
            Binder {
                var: y,
                body: contr,
            },
        ))
    }
    pub fn equiv_type(&mut self, a: ValId, b: ValId) -> ValId {
        let x = self.fresh_term();
        let arrow = self.alloc(Val::Pi(a, Binder { var: x, body: b }));
        let f = self.fresh_term();
        let fv = self.alloc(Val::Var(f, Some(arrow)));
        let proof = self.is_equiv(a, b, fv);
        self.alloc(Val::Sigma(
            arrow,
            Binder {
                var: f,
                body: proof,
            },
        ))
    }
    /// Contractibility of the identity fiber, by filling a square with its
    /// upper edge at y, left edge at y, and right edge at the input path.
    /// The same expansion is checked as an ordinary library term in prelude.kamo.
    pub fn identity_equiv(&mut self, a: ValId) -> ValId {
        let x = self.fresh_term();
        let xv = self.alloc(Val::Var(x, Some(a)));
        let identity = self.alloc(Val::Lam(Binder { var: x, body: xv }));
        let y = self.fresh_term();
        let yv = self.alloc(Val::Var(y, Some(a)));
        let fiber = self.fiber(a, a, identity, yv);
        let h = self.fresh_term();
        let hv = self.alloc(Val::Var(h, Some(fiber)));
        let p = self.snd(hv);
        let refl_dim = self.fresh_dim();
        let refl = self.alloc(Val::PLam(Binder {
            var: refl_dim,
            body: yv,
        }));
        let center = self.alloc(Val::Pair(yv, refl));
        let i = self.fresh_dim();
        let j = self.fresh_dim();
        let k = self.fresh_dim();
        let pk = self.at(p, Dim::Var(k));
        let i0 = self.faces.eq(Dim::Var(i), Dim::Zero);
        let i1 = self.faces.eq(Dim::Var(i), Dim::One);
        let square = self.alloc(Val::Com(Composition {
            dim: k,
            family: a,
            from: Dim::One,
            to: Dim::Var(j),
            cap: yv,
            tubes: vec![(i0, yv), (i1, pk)],
        }));
        let first = self.restrict(square, j, Dim::Zero);
        let second = self.alloc(Val::PLam(Binder {
            var: j,
            body: square,
        }));
        let pair = self.alloc(Val::Pair(first, second));
        let contraction = self.alloc(Val::PLam(Binder { var: i, body: pair }));
        let contraction = self.alloc(Val::Lam(Binder {
            var: h,
            body: contraction,
        }));
        let proof = self.alloc(Val::Pair(center, contraction));
        let proof = self.alloc(Val::Lam(Binder {
            var: y,
            body: proof,
        }));
        self.alloc(Val::Pair(identity, proof))
    }
    fn glue_fiber_element(&mut self, g: ValId, v: ValId) -> ValId {
        let base = self.alloc(Val::Unglue(g, v));
        let i = self.fresh_dim();
        let path = self.alloc(Val::PLam(Binder { var: i, body: base }));
        self.alloc(Val::Pair(v, path))
    }
    pub fn compose_glue(
        &mut self,
        mut c: Composition,
        base: ValId,
        branches: Vec<(FaceId, ValId, ValId)>,
    ) -> Result<ValId> {
        // Retain the exposed Glue data: re-evaluating the original type after
        // an interval substitution may instead expose its boundary type.
        c.family = self.alloc(Val::Glue(base, branches.clone()));
        // Alignment: add the prescribed composition on every universally
        // valid Glue face before executing incoherent composition.
        let original = c.clone();
        for &(f, t, _) in &branches {
            let all = self.faces.forall(c.dim, f)?;
            if self.faces.inconsistent(all)? {
                continue;
            }
            let y = self.fresh_dim();
            let fill = self.alloc(Val::Com(Composition {
                family: t,
                to: Dim::Var(y),
                ..original.clone()
            }));
            let fill = self.restrict(fill, y, Dim::Var(c.dim));
            c.tubes.push((all, fill));
        }
        let source_g = self.restrict(c.family, c.dim, c.from);
        let target_g = self.restrict(c.family, c.dim, c.to);
        let cap = self.alloc(Val::Unglue(source_g, c.cap));
        let tubes = c
            .tubes
            .iter()
            .map(|(f, t)| (*f, self.alloc(Val::Unglue(c.family, *t))))
            .collect();
        let base_prime = self.alloc(Val::Com(Composition {
            family: base,
            cap,
            tubes,
            ..c.clone()
        }));
        let target_base = self.restrict(base, c.dim, c.to);
        let same = self.faces.eq(c.from, c.to);
        let mut partial = c
            .tubes
            .iter()
            .map(|(f, t)| (*f, self.restrict(*t, c.dim, c.to)))
            .collect::<Vec<_>>();
        partial.push((same, c.cap));
        let correction_dim = self.fresh_dim();
        let mut correction_tubes = vec![];
        let mut tops = vec![];
        for (f, t, e) in branches {
            let f = self.restrict_face(f, c.dim, c.to);
            let t = self.restrict(t, c.dim, c.to);
            let e = self.restrict(e, c.dim, c.to);
            let fun = self.fst(e);
            let fiber = self.fiber(t, target_base, fun, base_prime);
            let witness = self.snd(e);
            let witness = self.app(witness, base_prime);
            let center = self.fst(witness);
            let contraction = self.snd(witness);
            let ext_dim = self.fresh_dim();
            let mut extensions = vec![];
            for &(boundary, g) in &partial {
                let h = self.glue_fiber_element(target_g, g);
                let path = self.app(contraction, h);
                let v = self.at(path, Dim::Var(ext_dim));
                extensions.push((boundary, v));
            }
            let extended = self.alloc(Val::Com(Composition {
                dim: ext_dim,
                family: fiber,
                from: Dim::Zero,
                to: Dim::One,
                cap: center,
                tubes: extensions,
            }));
            let top = self.fst(extended);
            tops.push((f, top));
            let path = self.snd(extended);
            let line = self.at(path, Dim::Var(correction_dim));
            correction_tubes.push((f, line));
        }
        for (f, g) in partial {
            let b = self.alloc(Val::Unglue(target_g, g));
            correction_tubes.push((f, b));
        }
        let corrected = self.alloc(Val::Com(Composition {
            dim: correction_dim,
            family: target_base,
            from: Dim::One,
            to: Dim::Zero,
            cap: base_prime,
            tubes: correction_tubes,
        }));
        Ok(self.alloc(Val::GlueIntro(corrected, tops)))
    }
    pub fn compose_universe(&mut self, c: Composition) -> ValId {
        let mut branches = vec![];
        for (face, t) in c.tubes {
            let target = self.restrict(t, c.dim, c.to);
            let x = self.fresh_term();
            let xv = self.alloc(Val::Var(x, Some(target)));
            let coerced = self.alloc(Val::Com(Composition {
                dim: c.dim,
                family: t,
                from: c.to,
                to: c.from,
                cap: xv,
                tubes: vec![],
            }));
            let fun = self.alloc(Val::Lam(Binder {
                var: x,
                body: coerced,
            }));
            let j = self.fresh_dim();
            let tj = self.restrict(t, c.dim, Dim::Var(j));
            let cj = self.alloc(Val::Com(Composition {
                dim: c.dim,
                family: t,
                from: c.to,
                to: Dim::Var(j),
                cap: xv,
                tubes: vec![],
            }));
            let fj = self.alloc(Val::Lam(Binder { var: x, body: cj }));
            let proof_family = self.is_equiv(target, tj, fj);
            let identity = self.identity_equiv(target);
            let identity_proof = self.snd(identity);
            let proof = self.alloc(Val::Com(Composition {
                dim: j,
                family: proof_family,
                from: c.to,
                to: c.from,
                cap: identity_proof,
                tubes: vec![],
            }));
            let equivalence = self.alloc(Val::Pair(fun, proof));
            branches.push((face, target, equivalence));
        }
        let same = self.faces.eq(c.from, c.to);
        let identity = self.identity_equiv(c.cap);
        branches.push((same, c.cap, identity));
        self.alloc(Val::Glue(c.cap, branches))
    }
}
