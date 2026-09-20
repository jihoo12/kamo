use crate::eval::{Engine,Val,ValId};
use crate::face::{Dim,FaceId};
use crate::{Error,Result};

#[derive(Default)]
struct Names { terms:Vec<u32>, dims:Vec<u32> }
impl Names {
    fn dim(&self,d:Dim)->Result<String> {match d {Dim::Zero=>Ok("0".into()),Dim::One=>Ok("1".into()),Dim::Var(x)=>self.dims.iter().position(|y|*y==x).map(|i|format!("i{i}")).ok_or_else(||Error::plain("internal error: escaped interval variable"))}}
}
impl Engine<'_> {
    pub fn quote(&mut self,v:ValId,ty:ValId,face:FaceId)->Result<String> {self.quote_inner(v,Some(ty),face,&mut Names::default())}
    fn quote_inner(&mut self,v:ValId,ty:Option<ValId>,face:FaceId,n:&mut Names)->Result<String> {
        self.tick()?;
        if let Some(ty)=ty {
            let ty=self.force(ty,face)?;
            match self.get(ty) {
                Val::Pi(a,b)=>{let x=self.variable(a);let Val::Var(level,_)=self.get(x) else{unreachable!()};let name=format!("x{}",n.terms.len());n.terms.push(level);let body=self.app(v,x);let b=self.inst(&b,x);let body=self.quote_inner(body,Some(b),face,n)?;n.terms.pop();return Ok(format!("(lam {name} {body})"));},
                Val::Sigma(a,b)=>{let x=self.fst(v);let y=self.snd(v);let b=self.inst(&b,x);let x=self.quote_inner(x,Some(a),face,n)?;let y=self.quote_inner(y,Some(b),face,n)?;return Ok(format!("(pair {x} {y})"));},
                Val::Path(b,_,_)=>{let i=self.fresh_dim();let name=format!("i{}",n.dims.len());n.dims.push(i);let body=self.at(v,Dim::Var(i));let ty=self.inst_dim(&b,Dim::Var(i));let body=self.quote_inner(body,Some(ty),face,n)?;n.dims.pop();return Ok(format!("(path {name} {body})"));},
                Val::Glue(base,branches)=>{
                    let g=self.quote_inner(ty,None,face,n)?;let unglued=self.alloc(Val::Unglue(ty,v));let base=self.quote_inner(unglued,Some(base),face,n)?;let mut tops=vec![];
                    for (f,a,_) in branches {let under=self.faces.and(face,f);if self.faces.inconsistent(under)?{continue;}let ff=self.faces.display(f,&n.dims);let top=self.quote_inner(v,Some(a),under,n)?;tops.push(format!("({ff} {top})"));}
                    return Ok(format!("(glue {g} {base} ({}))",tops.join(" ")));
                },
                _=>{},
            }
        }
        let v=self.force(v,face)?;
        Ok(match self.get(v) {
            Val::Var(x,_)=>format!("x{}",n.terms.iter().position(|y|*y==x).ok_or_else(||Error::plain("internal error: escaped term variable"))?),
            Val::U(l)=>format!("(U {l})"),Val::Bool=>"Bool".into(),Val::Nat=>"Nat".into(),Val::True=>"true".into(),Val::False=>"false".into(),Val::Zero=>"zero".into(),
            Val::Pi(a,b)|Val::Sigma(a,b)=>{
                let op=if matches!(self.get(v),Val::Pi(..)){"Pi"}else{"Sigma"};let domain=self.quote_inner(a,None,face,n)?;let x=self.variable(a);let Val::Var(level,_)=self.get(x) else{unreachable!()};let name=format!("x{}",n.terms.len());n.terms.push(level);let body=self.inst(&b,x);let body=self.quote_inner(body,None,face,n)?;n.terms.pop();format!("({op} {name} {domain} {body})")
            },
            Val::Path(b,l,r)=>{
                let i=self.fresh_dim();let name=format!("i{}",n.dims.len());n.dims.push(i);let body=self.inst_dim(&b,Dim::Var(i));let body=self.quote_inner(body,None,face,n)?;n.dims.pop();let lty=self.inst_dim(&b,Dim::Zero);let rty=self.inst_dim(&b,Dim::One);let l=self.quote_inner(l,Some(lty),face,n)?;let r=self.quote_inner(r,Some(rty),face,n)?;format!("(Path {name} {body} {l} {r})")
            },
            Val::Suc(k)=>{let nat=self.alloc(Val::Nat);format!("(suc {})",self.quote_inner(k,Some(nat),face,n)?)},
            Val::App(f,a)=>{
                let fty=self.neutral_type(f,face)?;let fty=self.force(fty,face)?;let argty=if let Val::Pi(a,_)=self.get(fty){Some(a)}else{None};let f=self.quote_inner(f,None,face,n)?;let a=self.quote_inner(a,argty,face,n)?;format!("(app {f} {a})")
            },
            Val::Fst(p)=>format!("(fst {})",self.quote_inner(p,None,face,n)?),Val::Snd(p)=>format!("(snd {})",self.quote_inner(p,None,face,n)?),
            Val::PApp(p,d)=>format!("(at {} {})",self.quote_inner(p,None,face,n)?,n.dim(d)?),
            Val::If(p,a,b,c)=>{
                let bool_ty=self.alloc(Val::Bool);let x=self.variable(bool_ty);let Val::Var(level,_)=self.get(x) else{unreachable!()};let name=format!("x{}",n.terms.len());n.terms.push(level);let px=self.app(p,x);let motive=self.quote_inner(px,None,face,n)?;n.terms.pop();
                let tv=self.alloc(Val::True);let fv=self.alloc(Val::False);let at=self.app(p,tv);let bt=self.app(p,fv);let a=self.quote_inner(a,Some(at),face,n)?;let b=self.quote_inner(b,Some(bt),face,n)?;let c=self.quote_inner(c,Some(bool_ty),face,n)?;format!("(bool-elim (lam {name} {motive}) {a} {b} {c})")
            },
            Val::NatElim(p,z,s,k)=>{
                let nat=self.alloc(Val::Nat);let x=self.variable(nat);let Val::Var(level,_)=self.get(x) else{unreachable!()};let name=format!("x{}",n.terms.len());n.terms.push(level);let px=self.app(p,x);let motive=self.quote_inner(px,None,face,n)?;
                let ih=self.variable(px);let Val::Var(ihlevel,_)=self.get(ih) else{unreachable!()};let ihname=format!("x{}",n.terms.len());n.terms.push(ihlevel);let step=self.app(s,x);let step=self.app(step,ih);let suc=self.alloc(Val::Suc(x));let sty=self.app(p,suc);let step=self.quote_inner(step,Some(sty),face,n)?;n.terms.pop();n.terms.pop();
                let zero=self.alloc(Val::Zero);let zty=self.app(p,zero);let z=self.quote_inner(z,Some(zty),face,n)?;let k=self.quote_inner(k,Some(nat),face,n)?;format!("(nat-elim (lam {name} {motive}) {z} (lam {name} (lam {ihname} {step})) {k})")
            },
            Val::Com(c)=>{
                let from=n.dim(c.from)?;let to=n.dim(c.to)?;let src=self.restrict(c.family,c.dim,c.from);let cap=self.quote_inner(c.cap,Some(src),face,n)?;
                let name=format!("i{}",n.dims.len());n.dims.push(c.dim);let family=self.quote_inner(c.family,None,face,n)?;let mut bs=vec![];
                for (f,v) in c.tubes {let under=self.faces.and(face,f);if self.faces.inconsistent(under)?{continue;}let ff=self.faces.display(f,&n.dims);let body=self.quote_inner(v,Some(c.family),under,n)?;bs.push(format!("({ff} {body})"));}n.dims.pop();
                format!("(com {name} {family} {from} {to} {cap} ({}))",bs.join(" "))
            },
            Val::System(a,bs)=>{
                let ty=self.quote_inner(a,None,face,n)?;let mut out=vec![];for (f,v) in bs {let under=self.faces.and(face,f);if self.faces.inconsistent(under)?{continue;}let ff=self.faces.display(f,&n.dims);let v=self.quote_inner(v,Some(a),under,n)?;out.push(format!("({ff} {v})"));}format!("(system {ty} ({}))",out.join(" "))
            },
            Val::Glue(base,branches)=>{
                let b=self.quote_inner(base,None,face,n)?;let mut out=vec![];for (f,a,e) in branches {let under=self.faces.and(face,f);if self.faces.inconsistent(under)?{continue;}let ff=self.faces.display(f,&n.dims);let eqty=self.equiv_type(a,base);let a=self.quote_inner(a,None,under,n)?;let e=self.quote_inner(e,Some(eqty),under,n)?;out.push(format!("({ff} {a} {e})"));}format!("(Glue {b} ({}))",out.join(" "))
            },
            Val::Unglue(g,v)=>format!("(unglue {} {})",self.quote_inner(g,None,face,n)?,self.quote_inner(v,None,face,n)?),
            Val::GlueIntro(_,_)=>return Err(Error::plain("internal error: quotation needs the Glue type")),
            Val::Lam(_)|Val::PLam(_)|Val::Pair(_,_)=>return Err(Error::plain("internal error: quotation needs an introduction form's type")),
            Val::Susp(_,_)|Val::Sub(_,_)=>unreachable!("force removes suspension heads"),
        })
    }
}
