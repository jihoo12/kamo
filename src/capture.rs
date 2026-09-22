//! Free de Bruijn slots needed by evaluation, not by checking annotations.
use crate::hash::IdMap;
use crate::syntax::{D, F, Program, Term, TermId};
use std::collections::BTreeSet;
pub(crate) type Slots = (Vec<usize>, Vec<usize>);
pub(crate) fn slots(p: &Program, t: TermId, cache: &mut IdMap<TermId, Slots>) -> Slots {
    if let Some(s) = cache.get(&t) {
        return s.clone();
    }
    let mut ts = BTreeSet::new();
    let mut ds = BTreeSet::new();
    let mut children = Vec::new();
    fn dim(d: D, ds: &mut BTreeSet<usize>) {
        if let D::Bound(i) = d {
            ds.insert(i);
        }
    }
    fn face(f: &F, ds: &mut BTreeSet<usize>) {
        match f {
            F::Eq(a, b) => {
                dim(*a, ds);
                dim(*b, ds);
            }
            F::And(a, b) | F::Or(a, b) => {
                face(a, ds);
                face(b, ds);
            }
            _ => {}
        }
    }
    match &p.terms.get(t).term {
        Term::Var(i) => {
            ts.insert(*i);
        }
        Term::Pi(a, b) | Term::Sigma(a, b) => {
            children.push((*a, 0, 0));
            children.push((*b, 1, 0));
        }
        Term::Lam(b) => children.push((*b, 1, 0)),
        Term::PLam(b) => children.push((*b, 0, 1)),
        Term::Path(a, l, r) => {
            children.push((*a, 0, 1));
            children.push((*l, 0, 0));
            children.push((*r, 0, 0));
        }
        Term::App(a, b) | Term::Pair(a, b) | Term::Unglue(a, b) => {
            children.push((*a, 0, 0));
            children.push((*b, 0, 0));
        }
        Term::Fst(a) | Term::Snd(a) | Term::Suc(a) | Term::Ann(a, _) => children.push((*a, 0, 0)),
        Term::If(a, b, c, d) | Term::NatElim(a, b, c, d) => {
            for x in [a, b, c, d] {
                children.push((*x, 0, 0));
            }
        }
        Term::PApp(p, d) => {
            children.push((*p, 0, 0));
            dim(*d, &mut ds);
        }
        Term::Com {
            family,
            from,
            to,
            cap,
            tubes,
        } => {
            children.push((*family, 0, 1));
            children.push((*cap, 0, 0));
            dim(*from, &mut ds);
            dim(*to, &mut ds);
            for (f, t) in tubes {
                face(f, &mut ds);
                children.push((*t, 0, 1));
            }
        }
        Term::System(a, bs) | Term::GlueIntro(_, a, bs) => {
            children.push((*a, 0, 0));
            for (f, t) in bs {
                face(f, &mut ds);
                children.push((*t, 0, 0));
            }
        }
        Term::Glue(a, bs) => {
            children.push((*a, 0, 0));
            for (f, t, e) in bs {
                face(f, &mut ds);
                children.push((*t, 0, 0));
                children.push((*e, 0, 0));
            }
        }
        _ => {}
    }
    for (c, nt, nd) in children {
        let (a, b) = slots(p, c, cache);
        ts.extend(a.into_iter().filter_map(|i| i.checked_sub(nt)));
        ds.extend(b.into_iter().filter_map(|i| i.checked_sub(nd)));
    }
    let result = (ts.into_iter().collect(), ds.into_iter().collect());
    cache.insert(t, result.clone());
    result
}
