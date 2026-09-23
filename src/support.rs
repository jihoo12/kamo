//! Conservative free-variable support for skipping irrelevant substitutions.
use super::*;
use std::collections::BTreeSet;
#[derive(Clone, Default)]
pub(super) struct Support {
    terms: BTreeSet<u32>,
    dims: BTreeSet<u32>,
}
impl Support {
    fn union(&mut self, other: Self) {
        self.terms.extend(other.terms);
        self.dims.extend(other.dims);
    }
    fn dim(&mut self, d: Dim) {
        if let Dim::Var(x) = d {
            self.dims.insert(x);
        }
    }
}
impl Engine<'_> {
    pub(crate) fn relevant_quote_face(
        &mut self,
        v: ValId,
        ty: Option<ValId>,
        face: FaceId,
        terms: &mut [Option<u32>],
        dims: &mut [Option<u32>],
    ) -> Result<FaceId> {
        self.computing_support = true;
        let mut budget = 4096;
        let mut free = self.value_support(v, &mut budget, 0);
        if let Some(ty) = ty {
            free = free.and_then(|mut free| {
                free.union(self.value_support(ty, &mut budget, 0)?);
                Some(free)
            });
        }
        self.computing_support = false;
        match free {
            Some(free) => {
                for level in terms {
                    if level.is_some_and(|x| !free.terms.contains(&x)) {
                        *level = None;
                    }
                }
                for level in dims {
                    if level.is_some_and(|x| !free.dims.contains(&x)) {
                        *level = None;
                    }
                }
                self.faces.project(face, &free.dims)
            }
            None => Ok(face),
        }
    }

    // Keeping a binder's existing level is safe only when every component of
    // the substitution leaves it untouched and cannot capture it in an image.
    pub(super) fn preserves_binder(&mut self, s: SubId, var: u32, dim: bool) -> bool {
        if self.computing_support {
            return false;
        }
        self.computing_support = true;
        let mut work = vec![s];
        let mut budget = 4096;
        let mut safe = true;
        while let Some(s) = work.pop() {
            if budget == 0 {
                safe = false;
                break;
            }
            budget -= 1;
            let s = self.subs.get(s).clone();
            if let Some((a, b)) = s.compose {
                work.extend([a, b]);
            }
            if dim && s.dims.iter().any(|(x, d)| *x == var || *d == Dim::Var(var)) {
                safe = false;
                break;
            }
            for (x, image) in s.terms {
                if !dim && x == var {
                    safe = false;
                    break;
                }
                let Some(free) = self.value_support(image, &mut budget, 0) else {
                    safe = false;
                    break;
                };
                if if dim {
                    free.dims.contains(&var)
                } else {
                    free.terms.contains(&var)
                } {
                    safe = false;
                    break;
                }
            }
            if !safe {
                break;
            }
        }
        self.computing_support = false;
        safe
    }

    pub(super) fn irrelevant(&mut self, v: ValId, s: SubId) -> bool {
        self.computing_support = true;
        let support = self.value_support(v, &mut 4096, 0);
        self.computing_support = false;
        support.is_some_and(|free| {
            free.terms.into_iter().all(|x| !self.maps_term(s, x))
                && free
                    .dims
                    .into_iter()
                    .all(|x| self.sub_dim(s, Dim::Var(x)) == Dim::Var(x))
        })
    }
    fn maps_term(&self, s: SubId, x: u32) -> bool {
        let s = self.subs.get(s);
        if let Some((a, b)) = s.compose {
            self.maps_term(a, x) || self.maps_term(b, x)
        } else {
            s.terms.iter().any(|(y, _)| *y == x)
        }
    }
    fn value_support(&mut self, v: ValId, budget: &mut usize, depth: usize) -> Option<Support> {
        if let Some(s) = self.support_cache.get(&v) {
            return s.clone();
        }
        if *budget == 0 || depth > 128 {
            return None;
        }
        *budget -= 1;
        let result = self.support_inner(v, budget, depth + 1);
        if result.is_some() {
            self.support_cache.insert(v, result.clone());
        }
        result
    }
    fn support_inner(&mut self, v: ValId, budget: &mut usize, depth: usize) -> Option<Support> {
        let mut result = Support::default();
        let mut children = Vec::new();
        match self.get(v) {
            Val::Var(x, ty) => {
                result.terms.insert(x);
                children.extend(ty);
            }
            Val::Susp(_, e) => {
                let env = self.environment(e);
                children.extend(env.terms);
                for d in env.dims {
                    result.dim(d);
                }
            }
            Val::Sub(v, s) => {
                let source = self.value_support(v, budget, depth)?;
                for x in source.terms {
                    if let Some(image) = self.sub_term(s, x) {
                        result.union(self.value_support(image, budget, depth)?);
                    } else {
                        result.terms.insert(x);
                    }
                }
                for x in source.dims {
                    result.dim(self.sub_dim(s, Dim::Var(x)));
                }
            }
            Val::Pi(a, b) | Val::Sigma(a, b) => {
                let mut body = self.value_support(b.body, budget, depth)?;
                body.terms.remove(&b.var);
                result.union(body);
                children.push(a);
            }
            Val::Lam(b) => {
                result = self.value_support(b.body, budget, depth)?;
                result.terms.remove(&b.var);
            }
            Val::PLam(b) => {
                result = self.value_support(b.body, budget, depth)?;
                result.dims.remove(&b.var);
            }
            Val::Path(b, l, r) => {
                result = self.value_support(b.body, budget, depth)?;
                result.dims.remove(&b.var);
                children.extend([l, r]);
            }
            Val::App(a, b) | Val::Pair(a, b) | Val::Unglue(a, b) => children.extend([a, b]),
            Val::Fst(a) | Val::Snd(a) | Val::Suc(a) => children.push(a),
            Val::PApp(a, d) => {
                children.push(a);
                result.dim(d);
            }
            Val::If(p, a, b, c) | Val::NatElim(p, a, b, c) => children.extend([p, a, b, c]),
            Val::Com(c) => {
                let mut bound = self.value_support(c.family, budget, depth)?;
                for (f, t) in c.tubes {
                    bound.union(self.value_support(t, budget, depth)?);
                    for d in self.faces.dimensions(f) {
                        result.dim(d);
                    }
                }
                bound.dims.remove(&c.dim);
                result.union(bound);
                result.dim(c.from);
                result.dim(c.to);
                children.push(c.cap);
            }
            Val::Glue(a, bs) => {
                children.push(a);
                for (f, t, e) in bs {
                    children.extend([t, e]);
                    for d in self.faces.dimensions(f) {
                        result.dim(d);
                    }
                }
            }
            Val::System(a, bs) | Val::GlueIntro(a, bs) => {
                children.push(a);
                for (f, t) in bs {
                    children.push(t);
                    for d in self.faces.dimensions(f) {
                        result.dim(d);
                    }
                }
            }
            _ => {}
        }
        for c in children {
            result.union(self.value_support(c, budget, depth)?);
        }
        Some(result)
    }
}
