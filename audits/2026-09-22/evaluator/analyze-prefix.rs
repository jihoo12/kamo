// Exact hash-consing of printed S-expressions (no hash-only equality decisions).
// Input may be an explicitly marked incomplete diagnostic prefix.
use std::{collections::HashMap,fs};
fn main(){
 let path=std::env::args().nth(1).expect("prefix path");let data=fs::read_to_string(path).unwrap();let bytes=data.as_bytes();
 let mut atoms:HashMap<&str,usize>=HashMap::new();let mut lists:HashMap<Vec<usize>,usize>=HashMap::new();
 let mut sizes=Vec::new();let mut counts=Vec::new();let mut first=Vec::new();let mut stack:Vec<(usize,Vec<usize>)>=Vec::new();let mut i=0;let mut occurrences=0usize;
 while i<bytes.len(){match bytes[i]{
 b'('=>{stack.push((i,Vec::new()));i+=1;}
 b')'=>{let(start,children)=stack.pop().unwrap();let id=if let Some(id)=lists.get(&children){*id}else{let id=sizes.len();sizes.push(i-start+1);counts.push(0usize);first.push(start);lists.insert(children,id);id};counts[id]+=1;occurrences+=1;if let Some((_,p))=stack.last_mut(){p.push(id);}i+=1;}
 b if b.is_ascii_whitespace()=>i+=1,
 _=>{let start=i;while i<bytes.len()&&!b"() \n\t\r".contains(&bytes[i]){i+=1;}if i==bytes.len(){break;}let atom=&data[start..i];let id=*atoms.entry(atom).or_insert_with(||{let id=sizes.len();sizes.push(atom.len());counts.push(0);first.push(start);id});counts[id]+=1;if let Some((_,p))=stack.last_mut(){p.push(id);}}
 }}
 println!("bytes={} complete_lists={} unique_lists={} unique_atoms={} unfinished_depth={}",data.len(),occurrences,lists.len(),atoms.len(),stack.len());
 let mut repeated:Vec<_>=(0..sizes.len()).filter(|i|counts[*i]>1&&sizes[*i]>1000).collect();repeated.sort_by_key(|i|std::cmp::Reverse(sizes[*i]*counts[*i]));
 for id in repeated.into_iter().take(12){println!("repeated bytes={} occurrences={} first_offset={} prefix={:?}",sizes[id],counts[id],first[id],&data[first[id]..(first[id]+80).min(data.len())]);}
 for(start,_)in stack.iter().take(16){println!("unfinished offset={} prefix={:?}",start,&data[*start..(*start+80).min(data.len())]);}
}
