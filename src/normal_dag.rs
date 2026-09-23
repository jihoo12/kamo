//! Owned shared text for fully reduced normal forms. No semantic IDs or thunks.
use crate::hash::IdMap;
use crate::{Error, Result};
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Node {
    Text(String),
    Concat(Vec<usize>),
}
#[derive(Debug)]
pub struct NormalDag {
    nodes: Vec<Node>,
    lengths: Vec<usize>,
    root: usize,
}
impl NormalDag {
    pub fn expanded_bytes(&self) -> usize {
        self.lengths[self.root]
    }
    pub fn nodes(&self) -> usize {
        self.nodes.len()
    }
    /// An acyclic, topologically numbered text grammar. `text` uses Rust string
    /// escapes; `concat` lists earlier node IDs. The last line names the root.
    pub fn encode(&self) -> String {
        use std::fmt::Write;
        let mut out = String::from("kamo-normal-dag-v1\n");
        for (id, node) in self.nodes.iter().enumerate() {
            match node {
                Node::Text(s) => {
                    writeln!(out, "{id} text {s:?}").unwrap();
                }
                Node::Concat(xs) => {
                    write!(out, "{id} concat").unwrap();
                    for x in xs {
                        write!(out, " {x}").unwrap();
                    }
                    out.push('\n');
                }
            }
        }
        writeln!(
            out,
            "root {} expanded-bytes {}",
            self.root,
            self.expanded_bytes()
        )
        .unwrap();
        out
    }
    pub fn materialize(&self, max_bytes: usize) -> Result<String> {
        if self.expanded_bytes() > max_bytes {
            return Err(Error::plain("quotation output byte budget exhausted"));
        }
        let mut out = String::new();
        out.try_reserve(self.expanded_bytes())
            .map_err(|_| Error::plain("quotation output allocation failed"))?;
        let mut work = vec![self.root];
        while let Some(id) = work.pop() {
            match &self.nodes[id] {
                Node::Text(s) => out.push_str(s),
                Node::Concat(xs) => work.extend(xs.iter().rev().copied()),
            }
        }
        Ok(out)
    }
}
#[derive(Clone, Copy)]
pub(crate) enum Saved {
    Text(usize, usize),
    Shared(usize),
}
pub(crate) struct Buffer {
    text: Option<String>,
    dag: NormalDag,
    intern: IdMap<Node, usize>,
    parts: Vec<usize>,
    expanded: usize,
    stored: usize,
    max_bytes: usize,
}
impl Buffer {
    pub fn new(shared: bool, max_bytes: usize) -> Self {
        Self {
            text: (!shared).then(String::new),
            dag: NormalDag {
                nodes: vec![],
                lengths: vec![],
                root: 0,
            },
            intern: IdMap::default(),
            parts: vec![],
            expanded: 0,
            stored: 0,
            max_bytes,
        }
    }
    pub fn shared(&self) -> bool {
        self.text.is_none()
    }
    pub fn len(&self) -> usize {
        self.expanded
    }
    pub fn nodes(&self) -> usize {
        self.dag.nodes.len()
    }
    #[cfg(test)]
    pub fn text(&self) -> Option<&str> {
        self.text.as_deref()
    }
    fn node(&mut self, node: Node, length: usize) -> Result<usize> {
        if let Some(id) = self.intern.get(&node) {
            return Ok(*id);
        }
        // Conservative budget for both arena payload and interned keys, plus
        // serialization. Hash table overhead is covered by the fixed allowance.
        let cost = 128
            + match &node {
                Node::Text(s) => 4 * s.len(),
                Node::Concat(xs) => 32 * xs.len(),
            };
        if cost > self.max_bytes.saturating_sub(self.stored) {
            return Err(Error::plain("shared normal-form storage budget exhausted"));
        }
        self.stored += cost;
        let id = self.dag.nodes.len();
        self.dag.nodes.push(node.clone());
        self.dag.lengths.push(length);
        self.intern.insert(node, id);
        Ok(id)
    }
    pub fn append(&mut self, s: &str) -> Result<()> {
        if let Some(out) = &mut self.text {
            if s.len() > self.max_bytes.saturating_sub(out.len()) {
                return Err(Error::plain("quotation output byte budget exhausted"));
            }
            out.try_reserve(s.len())
                .map_err(|_| Error::plain("quotation output allocation failed"))?;
            out.push_str(s);
        } else {
            let id = self.node(Node::Text(s.into()), s.len())?;
            self.parts.push(id);
        }
        self.expanded = self
            .expanded
            .checked_add(s.len())
            .ok_or_else(|| Error::plain("expanded normal form exceeds usize::MAX bytes"))?;
        Ok(())
    }
    pub fn seal(&mut self, start: usize) -> Result<Saved> {
        if self.text.is_some() {
            return Ok(Saved::Text(start, self.expanded));
        }
        let length = self.expanded - start;
        let mut remaining = length;
        let mut count = 0;
        while remaining != 0 {
            let id = self.parts[self.parts.len() - 1 - count];
            remaining = remaining
                .checked_sub(self.dag.lengths[id])
                .expect("quotation fragment boundary");
            count += 1;
        }
        let children = self.parts.split_off(self.parts.len() - count);
        let id = if children.len() == 1 {
            children[0]
        } else {
            self.node(Node::Concat(children), length)?
        };
        self.parts.push(id);
        Ok(Saved::Shared(id))
    }
    pub fn saved_len(&self, s: Saved) -> usize {
        match s {
            Saved::Text(a, b) => b - a,
            Saved::Shared(id) => self.dag.lengths[id],
        }
    }
    pub fn replay(&mut self, s: Saved) -> Result<()> {
        let length = self.saved_len(s);
        match s {
            Saved::Text(start, end) => {
                let out = self.text.as_mut().unwrap();
                if length > self.max_bytes.saturating_sub(out.len()) {
                    return Err(Error::plain("quotation output byte budget exhausted"));
                }
                out.try_reserve(length)
                    .map_err(|_| Error::plain("quotation output allocation failed"))?;
                out.extend_from_within(start..end);
            }
            Saved::Shared(id) => self.parts.push(id),
        }
        self.expanded = self
            .expanded
            .checked_add(length)
            .ok_or_else(|| Error::plain("expanded normal form exceeds usize::MAX bytes"))?;
        Ok(())
    }
    pub fn write_diagnostic(&mut self, path: impl AsRef<std::path::Path>) -> Result<()> {
        let result = if let Some(text) = &self.text {
            std::fs::write(path, text)
        } else {
            let Saved::Shared(root) = self.seal(0)? else {
                unreachable!()
            };
            self.dag.root = root;
            let encoded = self.dag.encode().replacen(
                "kamo-normal-dag-v1",
                "kamo-normal-dag-prefix-v1-INCOMPLETE",
                1,
            );
            std::fs::write(path, encoded)
        };
        result.map_err(|e| Error::plain(format!("cannot write diagnostic prefix: {e}")))
    }
    pub fn into_text(self) -> String {
        self.text.unwrap()
    }
    pub fn into_dag(mut self) -> Result<NormalDag> {
        let Saved::Shared(root) = self.seal(0)? else {
            unreachable!()
        };
        self.dag.root = root;
        Ok(self.dag)
    }
}
