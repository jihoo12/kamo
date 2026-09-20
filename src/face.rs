//! Positive Cartesian face logic. A dimension is not a Boolean.
use std::collections::{BTreeMap,HashMap};
use std::cell::RefCell;
use crate::arena::{Arena, key};
use crate::{Error,Result};
key!(FaceId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Dim { Zero, One, Var(u32) }
#[derive(Clone, Debug,PartialEq,Eq,Hash)]
enum Face { Top, Bot, Eq(Dim, Dim), And(FaceId, FaceId), Or(FaceId, FaceId) }
#[derive(Default)]
pub(crate) struct Faces { nodes: Arena<FaceId, Face>, intern:HashMap<Face,FaceId>, dnf_cache:RefCell<HashMap<FaceId,Vec<Clause>>> }
type Clause = Vec<(Dim, Dim)>;
impl Faces {
    fn node(&mut self,f:Face)->FaceId {if let Some(id)=self.intern.get(&f){return *id;}let id=self.nodes.alloc(f.clone());self.intern.insert(f,id);id}
    pub fn top(&mut self) -> FaceId { self.node(Face::Top) }
    pub fn bot(&mut self) -> FaceId { self.node(Face::Bot) }
    pub fn eq(&mut self, a: Dim, b: Dim) -> FaceId {if a==b{return self.top();}if matches!((a,b),(Dim::Zero,Dim::One)|(Dim::One,Dim::Zero)){return self.bot();}self.node(Face::Eq(a.min(b),a.max(b))) }
    pub fn and(&mut self, a: FaceId, b: FaceId) -> FaceId {
        if a==b{return a;}match (self.nodes.get(a),self.nodes.get(b)) { (Face::Bot,_)|(_,Face::Bot)=>self.bot(),(Face::Top,_)=>b,(_,Face::Top)=>a,_=>self.node(Face::And(a,b)) }
    }
    pub fn or(&mut self, a: FaceId, b: FaceId) -> FaceId {
        if a==b{return a;}match (self.nodes.get(a),self.nodes.get(b)) { (Face::Top,_)|(_,Face::Top)=>self.top(),(Face::Bot,_)=>b,(_,Face::Bot)=>a,_=>self.node(Face::Or(a,b)) }
    }
    pub fn substitute(&mut self, f: FaceId, map: &impl Fn(Dim) -> Dim) -> FaceId {
        match self.nodes.get(f).clone() {
            Face::Top => self.top(), Face::Bot => self.bot(),
            Face::Eq(a,b) => self.eq(map(a),map(b)),
            Face::And(a,b) => { let a=self.substitute(a,map); let b=self.substitute(b,map); self.and(a,b) },
            Face::Or(a,b) => { let a=self.substitute(a,map); let b=self.substitute(b,map); self.or(a,b) },
        }
    }
    fn dnf(&self, f: FaceId) -> Result<Vec<Clause>> {self.dnf_inner(f,0)}
    fn dnf_inner(&self, f: FaceId, depth:usize) -> Result<Vec<Clause>> {
        if depth>256 {return Err(Error::plain("face solver depth budget exhausted"));}
        if let Some(cached)=self.dnf_cache.borrow().get(&f){return Ok(cached.clone());}
        let raw=match self.nodes.get(f) {
            Face::Top => vec![vec![]], Face::Bot => vec![], Face::Eq(a,b) => vec![vec![(*a,*b)]],
            Face::Or(a,b) => { let mut a=self.dnf_inner(*a,depth+1)?; a.extend(self.dnf_inner(*b,depth+1)?); a },
            Face::And(a,b) => {
                let (a,b)=(self.dnf_inner(*a,depth+1)?,self.dnf_inner(*b,depth+1)?);
                if a.len().saturating_mul(b.len())>4096{return Err(Error::plain("face solver expansion budget exhausted"));}
                a.iter().flat_map(|x| b.iter().map(move |y| { let mut c=x.clone(); c.extend(y); c })).collect()
            }
        };
        let mut out:Vec<Clause>=vec![];
        for c in raw {
            if c.len()>1024{return Err(Error::plain("face solver clause budget exhausted"));}
            let p=Partition::new(&c);if p.equal(Dim::Zero,Dim::One){continue;}
            let c=p.0.keys().map(|x|(*x,p.root(*x))).collect::<Clause>();
            if out.iter().any(|weak|weak.iter().all(|(a,b)|p.equal(*a,*b))){continue;}
            out.retain(|strong| {let q=Partition::new(strong);!c.iter().all(|(a,b)|q.equal(*a,*b))});out.push(c);
        }
        if self.dnf_cache.borrow().len()<4096 && out.iter().map(Vec::len).sum::<usize>()<=64 {self.dnf_cache.borrow_mut().insert(f,out.clone());}Ok(out)
    }
    pub fn entails(&self, a: FaceId, b: FaceId) -> Result<bool> {
        let bs=self.dnf(b)?;
        Ok(self.dnf(a)?.iter().all(|clause| {
            let p=Partition::new(clause);
            p.equal(Dim::Zero,Dim::One) || bs.iter().any(|b| b.iter().all(|(x,y)| p.equal(*x,*y)))
        }))
    }
    pub fn inconsistent(&self, a: FaceId) -> Result<bool> {
        Ok(self.dnf(a)?.iter().all(|c| Partition::new(c).equal(Dim::Zero,Dim::One)))
    }
    pub fn equal(&self, a: FaceId, x: Dim, y: Dim) -> Result<bool> {
        Ok(self.dnf(a)?.iter().all(|c| { let p=Partition::new(c); p.equal(Dim::Zero,Dim::One)||p.equal(x,y) }))
    }
    pub fn clauses(&mut self, f: FaceId) -> Result<Vec<FaceId>> {
        Ok(self.dnf(f)?.into_iter().filter(|c| !Partition::new(c).equal(Dim::Zero,Dim::One)).map(|c| {
            let mut f=self.top(); for (a,b) in c { let e=self.eq(a,b); f=self.and(f,e); } f
        }).collect())
    }
    pub fn forall(&mut self, var:u32, f:FaceId)->Result<FaceId> {
        // A generic fresh dimension witnesses failure of every nontrivial
        // equality involving the quantified variable. This is not endpoint sampling.
        let mut out=self.bot();
        for c in self.dnf(f)? {
            if Partition::new(&c).equal(Dim::Zero,Dim::One){continue;}
            if c.iter().any(|(a,b)|a!=b&&(*a==Dim::Var(var)||*b==Dim::Var(var))){continue;}
            let mut clause=self.top();for (a,b) in c {if a!=b {let eq=self.eq(a,b);clause=self.and(clause,eq);}}
            out=self.or(out,clause);
        } Ok(out)
    }
    pub fn dimensions(&self,f:FaceId)->Vec<Dim> {
        let mut seen=std::collections::HashSet::new();let mut dims=std::collections::BTreeSet::new();let mut pending=vec![f];
        while let Some(f)=pending.pop(){if !seen.insert(f){continue;}match self.nodes.get(f){Face::Eq(a,b)=>{dims.insert(*a);dims.insert(*b);},Face::And(a,b)|Face::Or(a,b)=>{pending.push(*a);pending.push(*b);},_=>{}}}
        dims.into_iter().collect()
    }
    pub fn display(&self, f: FaceId, dims: &[u32]) -> String {
        fn d(x: Dim, ds: &[u32]) -> String { match x { Dim::Zero=>"0".into(),Dim::One=>"1".into(),Dim::Var(v)=>format!("i{}",ds.iter().position(|x| *x==v).unwrap_or(v as usize)) } }
        match self.nodes.get(f) {
            Face::Top=>"top".into(),Face::Bot=>"bottom".into(),
            Face::Eq(a,b)=>format!("(= {} {})",d(*a,dims),d(*b,dims)),
            Face::And(a,b)=>format!("(and {} {})",self.display(*a,dims),self.display(*b,dims)),
            Face::Or(a,b)=>format!("(or {} {})",self.display(*a,dims),self.display(*b,dims)),
        }
    }
    pub fn bytes(&self)->usize { self.nodes.bytes() }
    pub fn len(&self)->usize { self.nodes.len() }
}
struct Partition(BTreeMap<Dim,Dim>);
impl Partition {
    fn new(c: &Clause) -> Self {
        let mut p=Self(BTreeMap::new());
        for &(a,b) in c { let a=p.root(a); let b=p.root(b); if a!=b { p.0.insert(a.max(b),a.min(b)); } } p
    }
    fn root(&self, mut a: Dim) -> Dim { while let Some(b)=self.0.get(&a) { a=*b; } a }
    fn equal(&self,a: Dim,b: Dim)->bool { self.root(a)==self.root(b) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn interval_is_not_boolean() {
        let mut f=Faces::default(); let t=f.top(); let i=Dim::Var(0);
        let a=f.eq(i,Dim::Zero); let b=f.eq(i,Dim::One); let cover=f.or(a,b);
        assert!(!f.entails(t,cover).unwrap()); assert!(f.entails(a,cover).unwrap());
        let impossible=f.and(a,b); assert!(f.inconsistent(impossible).unwrap());
    }
    #[test] fn diagonals_and_transitivity() {
        let mut f=Faces::default(); let (i,j,k)=(Dim::Var(0),Dim::Var(1),Dim::Var(2));
        let a=f.eq(i,j); let b=f.eq(j,k); let c=f.and(a,b); let d=f.eq(i,k);
        assert!(f.entails(c,d).unwrap()); assert!(!f.entails(a,d).unwrap());
        let e=f.substitute(d,&|x| if x==k {i} else {x}); let t=f.top(); assert!(f.entails(t,e).unwrap());
    }
}
