//! Positive Cartesian face logic. A dimension is not a Boolean.
use crate::arena::{Arena, key};
use crate::hash::IdMap as HashMap;
use crate::{Error, Result};
use std::cell::RefCell;
use std::collections::BTreeMap;
key!(FaceId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Dim {
    Zero,
    One,
    Var(u32),
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Face {
    Top,
    Bot,
    Eq(Dim, Dim),
    And(FaceId, FaceId),
    Or(FaceId, FaceId),
}
#[derive(Default)]
pub(crate) struct Faces {
    nodes: Arena<FaceId, Face>,
    intern: HashMap<Face, FaceId>,
    dnf_cache: RefCell<HashMap<FaceId, Vec<Clause>>>,
}
type Clause = Vec<(Dim, Dim)>;
impl Faces {
    pub(crate) fn get(&self, f: FaceId) -> Face {
        self.nodes.get(f).clone()
    }
    fn node(&mut self, f: Face) -> FaceId {
        if let Some(id) = self.intern.get(&f) {
            return *id;
        }
        let id = self.nodes.alloc(f.clone());
        self.intern.insert(f, id);
        id
    }
    pub fn top(&mut self) -> FaceId {
        self.node(Face::Top)
    }
    pub fn bot(&mut self) -> FaceId {
        self.node(Face::Bot)
    }
    pub fn eq(&mut self, a: Dim, b: Dim) -> FaceId {
        if a == b {
            return self.top();
        }
        if matches!((a, b), (Dim::Zero, Dim::One) | (Dim::One, Dim::Zero)) {
            return self.bot();
        }
        self.node(Face::Eq(a.min(b), a.max(b)))
    }
    pub fn and(&mut self, a: FaceId, b: FaceId) -> FaceId {
        if a == b {
            return a;
        }
        match (self.nodes.get(a), self.nodes.get(b)) {
            (Face::Bot, _) | (_, Face::Bot) => self.bot(),
            (Face::Top, _) => b,
            (_, Face::Top) => a,
            _ => self.node(Face::And(a, b)),
        }
    }
    pub fn or(&mut self, a: FaceId, b: FaceId) -> FaceId {
        if a == b {
            return a;
        }
        match (self.nodes.get(a), self.nodes.get(b)) {
            (Face::Top, _) | (_, Face::Top) => self.top(),
            (Face::Bot, _) => b,
            (_, Face::Bot) => a,
            _ => self.node(Face::Or(a, b)),
        }
    }
    pub fn substitute(&mut self, f: FaceId, map: &impl Fn(Dim) -> Dim) -> FaceId {
        match self.nodes.get(f).clone() {
            Face::Top => self.top(),
            Face::Bot => self.bot(),
            Face::Eq(a, b) => self.eq(map(a), map(b)),
            Face::And(a, b) => {
                let a = self.substitute(a, map);
                let b = self.substitute(b, map);
                self.and(a, b)
            }
            Face::Or(a, b) => {
                let a = self.substitute(a, map);
                let b = self.substitute(b, map);
                self.or(a, b)
            }
        }
    }
    fn dnf(&self, f: FaceId) -> Result<Vec<Clause>> {
        self.dnf_inner(f, 0)
    }
    fn dnf_inner(&self, f: FaceId, depth: usize) -> Result<Vec<Clause>> {
        if depth > 256 {
            return Err(Error::plain("face solver depth budget exhausted"));
        }
        if let Some(cached) = self.dnf_cache.borrow().get(&f) {
            return Ok(cached.clone());
        }
        let raw = match self.nodes.get(f) {
            Face::Top => vec![vec![]],
            Face::Bot => vec![],
            Face::Eq(a, b) => vec![vec![(*a, *b)]],
            Face::Or(a, b) => {
                let mut a = self.dnf_inner(*a, depth + 1)?;
                a.extend(self.dnf_inner(*b, depth + 1)?);
                a
            }
            Face::And(a, b) => {
                let (a, b) = (
                    self.dnf_inner(*a, depth + 1)?,
                    self.dnf_inner(*b, depth + 1)?,
                );
                if a.len().saturating_mul(b.len()) > 4096 {
                    return Err(Error::plain("face solver expansion budget exhausted"));
                }
                a.iter()
                    .flat_map(|x| {
                        b.iter().map(move |y| {
                            let mut c = x.clone();
                            c.extend(y);
                            c
                        })
                    })
                    .collect()
            }
        };
        let mut out: Vec<Clause> = vec![];
        for c in raw {
            if c.len() > 1024 {
                return Err(Error::plain("face solver clause budget exhausted"));
            }
            let p = Partition::new(&c);
            if p.equal(Dim::Zero, Dim::One) {
                continue;
            }
            let c = p.0.keys().map(|x| (*x, p.root(*x))).collect::<Clause>();
            if out
                .iter()
                .any(|weak| weak.iter().all(|(a, b)| p.equal(*a, *b)))
            {
                continue;
            }
            out.retain(|strong| {
                let q = Partition::new(strong);
                !c.iter().all(|(a, b)| q.equal(*a, *b))
            });
            out.push(c);
        }
        if self.dnf_cache.borrow().len() < 4096 && out.iter().map(Vec::len).sum::<usize>() <= 64 {
            self.dnf_cache.borrow_mut().insert(f, out.clone());
        }
        Ok(out)
    }
    pub fn entails(&self, a: FaceId, b: FaceId) -> Result<bool> {
        let bs = self.dnf(b)?;
        Ok(self.dnf(a)?.iter().all(|clause| {
            let p = Partition::new(clause);
            p.equal(Dim::Zero, Dim::One)
                || bs.iter().any(|b| b.iter().all(|(x, y)| p.equal(*x, *y)))
        }))
    }
    pub fn inconsistent(&self, a: FaceId) -> Result<bool> {
        Ok(self
            .dnf(a)?
            .iter()
            .all(|c| Partition::new(c).equal(Dim::Zero, Dim::One)))
    }
    pub fn equal(&self, a: FaceId, x: Dim, y: Dim) -> Result<bool> {
        Ok(self.dnf(a)?.iter().all(|c| {
            let p = Partition::new(c);
            p.equal(Dim::Zero, Dim::One) || p.equal(x, y)
        }))
    }
    pub fn clauses(&mut self, f: FaceId) -> Result<Vec<FaceId>> {
        Ok(self
            .dnf(f)?
            .into_iter()
            .filter(|c| !Partition::new(c).equal(Dim::Zero, Dim::One))
            .map(|c| {
                let mut f = self.top();
                for (a, b) in c {
                    let e = self.eq(a, b);
                    f = self.and(f, e);
                }
                f
            })
            .collect())
    }
    /// Existentially forget dimensions outside `keep`, preserving every equality
    /// among retained dimensions and distinct endpoints (not Boolean sampling).
    pub(crate) fn project(
        &mut self,
        f: FaceId,
        keep: &std::collections::BTreeSet<u32>,
    ) -> Result<FaceId> {
        let mut out = self.bot();
        for clause in self.dnf(f)? {
            let partition = Partition::new(&clause);
            let mut representatives = BTreeMap::new();
            let mut projected = self.top();
            for d in [Dim::Zero, Dim::One]
                .into_iter()
                .chain(keep.iter().copied().map(Dim::Var))
            {
                let root = partition.root(d);
                if let Some(previous) = representatives.get(&root) {
                    let eq = self.eq(d, *previous);
                    projected = self.and(projected, eq);
                } else {
                    representatives.insert(root, d);
                }
            }
            out = self.or(out, projected);
        }
        Ok(out)
    }
    pub fn forall(&mut self, var: u32, f: FaceId) -> Result<FaceId> {
        // A generic fresh dimension witnesses failure of every nontrivial
        // equality involving the quantified variable. This is not endpoint sampling.
        let mut out = self.bot();
        for c in self.dnf(f)? {
            if Partition::new(&c).equal(Dim::Zero, Dim::One) {
                continue;
            }
            if c.iter()
                .any(|(a, b)| a != b && (*a == Dim::Var(var) || *b == Dim::Var(var)))
            {
                continue;
            }
            let mut clause = self.top();
            for (a, b) in c {
                if a != b {
                    let eq = self.eq(a, b);
                    clause = self.and(clause, eq);
                }
            }
            out = self.or(out, clause);
        }
        Ok(out)
    }
    pub fn dimensions(&self, f: FaceId) -> Vec<Dim> {
        let mut seen = std::collections::HashSet::new();
        let mut dims = std::collections::BTreeSet::new();
        let mut pending = vec![f];
        while let Some(f) = pending.pop() {
            if !seen.insert(f) {
                continue;
            }
            match self.nodes.get(f) {
                Face::Eq(a, b) => {
                    dims.insert(*a);
                    dims.insert(*b);
                }
                Face::And(a, b) | Face::Or(a, b) => {
                    pending.push(*a);
                    pending.push(*b);
                }
                _ => {}
            }
        }
        dims.into_iter().collect()
    }
    pub fn bytes(&self) -> usize {
        self.nodes.bytes()
    }
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
}
struct Partition(BTreeMap<Dim, Dim>);
impl Partition {
    fn new(c: &Clause) -> Self {
        let mut p = Self(BTreeMap::new());
        for &(a, b) in c {
            let a = p.root(a);
            let b = p.root(b);
            if a != b {
                p.0.insert(a.max(b), a.min(b));
            }
        }
        p
    }
    fn root(&self, mut a: Dim) -> Dim {
        while let Some(b) = self.0.get(&a) {
            a = *b;
        }
        a
    }
    fn equal(&self, a: Dim, b: Dim) -> bool {
        self.root(a) == self.root(b)
    }
}

impl Faces {
    /// Compact only between evaluator commands with an explicit complete root set.
    pub(crate) fn compact(&mut self, roots: &mut [FaceId]) -> Vec<usize> {
        use crate::arena::Key;
        let mut live = vec![false; self.nodes.len()];
        let mut work = roots.to_vec();
        while let Some(f) = work.pop() {
            if std::mem::replace(&mut live[f.index()], true) {
                continue;
            }
            if let Face::And(a, b) | Face::Or(a, b) = self.nodes.get(f) {
                work.extend([*a, *b]);
            }
        }
        let mut count = 0;
        let map: Vec<_> = live
            .iter()
            .map(|yes| {
                if *yes {
                    let i = count;
                    count += 1;
                    i
                } else {
                    usize::MAX
                }
            })
            .collect();
        let id = |f: FaceId| FaceId::new(map[f.index()]);
        let mut nodes = Arena::default();
        let mut intern = HashMap::default();
        for (i, yes) in live.iter().enumerate() {
            if *yes {
                let f = match self.nodes.get(FaceId::new(i)) {
                    Face::And(a, b) => Face::And(id(*a), id(*b)),
                    Face::Or(a, b) => Face::Or(id(*a), id(*b)),
                    f => f.clone(),
                };
                let key = nodes.alloc(f.clone());
                intern.insert(f, key);
            }
        }
        for root in roots {
            *root = id(*root);
        }
        self.nodes = nodes;
        self.intern = intern;
        self.dnf_cache.borrow_mut().clear();
        map
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn projection_preserves_transitive_equalities_without_booleanizing() {
        let mut f = Faces::default();
        let i = Dim::Var(0);
        let j = Dim::Var(1);
        let ij = f.eq(i, j);
        let i0 = f.eq(i, Dim::Zero);
        let j0 = f.eq(j, Dim::Zero);
        let under = f.and(ij, i0);
        let projected = f
            .project(under, &std::collections::BTreeSet::from([1]))
            .unwrap();
        assert!(f.entails(projected, j0).unwrap());
        assert!(f.entails(j0, projected).unwrap());
        let projected = f
            .project(ij, &std::collections::BTreeSet::from([1]))
            .unwrap();
        let top = f.top();
        assert!(f.entails(top, projected).unwrap());
        let i1 = f.eq(i, Dim::One);
        let endpoints = f.or(i0, i1);
        let retained = f
            .project(endpoints, &std::collections::BTreeSet::from([0]))
            .unwrap();
        assert!(!f.entails(top, retained).unwrap());
    }

    #[test]
    fn interval_is_not_boolean() {
        let mut f = Faces::default();
        let t = f.top();
        let i = Dim::Var(0);
        let a = f.eq(i, Dim::Zero);
        let b = f.eq(i, Dim::One);
        let cover = f.or(a, b);
        assert!(!f.entails(t, cover).unwrap());
        assert!(f.entails(a, cover).unwrap());
        let impossible = f.and(a, b);
        assert!(f.inconsistent(impossible).unwrap());
    }
    #[test]
    fn diagonals_and_transitivity() {
        let mut f = Faces::default();
        let (i, j, k) = (Dim::Var(0), Dim::Var(1), Dim::Var(2));
        let a = f.eq(i, j);
        let b = f.eq(j, k);
        let c = f.and(a, b);
        let d = f.eq(i, k);
        assert!(f.entails(c, d).unwrap());
        assert!(!f.entails(a, d).unwrap());
        let e = f.substitute(d, &|x| if x == k { i } else { x });
        let t = f.top();
        assert!(f.entails(t, e).unwrap());
    }

    #[test]
    fn quantification_uses_generic_dimensions() {
        let mut f = Faces::default();
        let i = Dim::Var(0);
        let j = Dim::Var(1);
        let i0 = f.eq(i, Dim::Zero);
        let i1 = f.eq(i, Dim::One);
        let j0 = f.eq(j, Dim::Zero);
        let endpoints = f.or(i0, i1);
        let quantified = f.forall(0, endpoints).unwrap();
        assert!(f.inconsistent(quantified).unwrap());
        let face = f.or(endpoints, j0);
        let quantified = f.forall(0, face).unwrap();
        assert!(f.entails(quantified, j0).unwrap());
        assert!(f.entails(j0, quantified).unwrap());
    }

    #[test]
    fn solver_depth_is_bounded() {
        let mut f = Faces::default();
        let mut face = f.top();
        for n in 0..300 {
            let e = f.eq(Dim::Var(n), Dim::Zero);
            face = f.and(face, e);
        }
        let top = f.top();
        assert!(f.entails(top, face).unwrap_err().message.contains("budget"));
    }
}
