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
    pub(super) fn irrelevant(&mut self, v: ValId, s: SubId) -> bool {
        self.computing_support = true;
        let support = self.value_support(v, &mut 512, 0);
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
        self.support_cache.insert(v, result.clone());
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
