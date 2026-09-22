#![forbid(unsafe_code)]
//! Experimental Cartesian cubical kernel with checked univalence library terms.
//! See README.md and docs/rules.md for the implemented rules and limitations.
mod arena;
mod capture;
mod check;
mod eval;
mod face;
mod glue;
mod hash;
mod quote;
mod syntax;

use std::fmt;
use std::time::{Duration, Instant};
pub type Result<T> = std::result::Result<T, Error>;
/// Bounds parser allocation; evaluation has separate work and arena budgets.
pub const MAX_SOURCE_BYTES: usize = 4 * 1024 * 1024;

#[derive(Clone, Debug)]
pub struct Error {
    pub offset: Option<usize>,
    pub message: String,
}
impl Error {
    fn at(offset: usize, message: impl Into<String>) -> Self {
        Self {
            offset: Some(offset),
            message: message.into(),
        }
    }
    fn plain(message: impl Into<String>) -> Self {
        Self {
            offset: None,
            message: message.into(),
        }
    }
    /// Byte offsets are rendered as one-based Unicode character columns.
    pub fn render(&self, file: &str, source: &str) -> String {
        if let Some(offset) = self.offset {
            let mut end = offset.min(source.len());
            while !source.is_char_boundary(end) {
                end -= 1;
            }
            let prefix = &source[..end];
            let line = prefix.bytes().filter(|b| *b == b'\n').count() + 1;
            let column = prefix.rsplit('\n').next().unwrap_or("").chars().count() + 1;
            format!("{file}:{line}:{column}: {}", self.message)
        } else {
            format!("{file}: {}", self.message)
        }
    }
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}
impl std::error::Error for Error {}

#[derive(Clone, Copy, Debug)]
pub struct Options {
    pub fuel: u64,
    pub optimized: bool,
    pub max_nodes: usize,
    /// Maximum UTF-8 bytes in the materialized normal form (default 16 MiB).
    pub max_output_bytes: usize,
    /// Maximum pending tasks on the iterative quotation stack.
    /// Quotation also consumes the shared fuel budget.
    pub max_quote_tasks: usize,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            fuel: 1_000_000,
            optimized: true,
            max_nodes: 250_000,
            max_output_bytes: 16 * 1024 * 1024,
            max_quote_tasks: 250_000,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Statistics {
    pub steps: u64,
    pub value_nodes: usize,
    pub environment_nodes: usize,
    pub substitution_nodes: usize,
    pub face_nodes: usize,
    /// Currently retained arena capacities, including Vec payloads. Excludes hash maps,
    /// allocator metadata, syntax, stack, and temporary face-solver allocations.
    pub arena_bytes: usize,
    pub cache_entries: usize,
    /// Fresh value nodes allocated over the entire session, excluding GC copies.
    pub allocated_values: usize,
    pub collections: usize,
    pub reclaimed_nodes: usize,
}
#[derive(Debug)]
pub struct NormalForm {
    pub text: String,
    pub statistics: Statistics,
}

/// Immutable checked syntax. Semantic IDs never cross this API boundary.
#[derive(Debug)]
pub struct CheckedProgram {
    program: syntax::Program,
}
impl CheckedProgram {
    pub fn check(source: &str) -> Result<Self> {
        Self::check_with(source, Options::default())
    }
    pub fn check_with(source: &str, options: Options) -> Result<Self> {
        if source.len() > MAX_SOURCE_BYTES {
            return Err(Error::plain("source size budget exceeded (maximum 4 MiB)"));
        }
        let program = syntax::parse(source)?;
        for index in 0..program.decls.len() {
            let mut engine =
                eval::Engine::new(&program, options.optimized, options.fuel, options.max_nodes);
            engine.check_declaration(index)?;
        }
        Ok(Self { program })
    }
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.program.decls.iter().map(|d| d.name.as_str())
    }
    pub fn normalize(&self, name: &str) -> Result<NormalForm> {
        self.normalize_with(name, Options::default())
    }
    pub fn normalize_with(&self, name: &str, options: Options) -> Result<NormalForm> {
        let decl = self
            .program
            .decls
            .iter()
            .find(|d| d.name == name)
            .ok_or_else(|| Error::plain(format!("unknown declaration '{name}'")))?;
        let mut engine = eval::Engine::new(
            &self.program,
            options.optimized,
            options.fuel,
            options.max_nodes,
        );
        let env = engine.env(eval::Env::default());
        let face = engine.faces.top();
        let ty = engine.thunk(decl.ty, env);
        let body = engine.thunk(decl.body, env);
        let text = engine.quote(
            body,
            ty,
            face,
            options.max_output_bytes,
            options.max_quote_tasks,
        )?;
        Ok(NormalForm {
            text,
            statistics: engine.statistics(),
        })
    }
    /// Measures semantic conversion of two checked definitions, without parsing,
    /// checking, quotation, or output inside the timed section.
    pub fn benchmark_conversion(
        &self,
        left: &str,
        right: &str,
        options: Options,
    ) -> Result<(Duration, Statistics, bool)> {
        let lookup = |name: &str| {
            self.program
                .decls
                .iter()
                .find(|d| d.name == name)
                .ok_or_else(|| Error::plain(format!("unknown declaration '{name}'")))
        };
        let left = lookup(left)?;
        let right = lookup(right)?;
        let mut engine = eval::Engine::new(
            &self.program,
            options.optimized,
            options.fuel,
            options.max_nodes,
        );
        let env = engine.env(eval::Env::default());
        let face = engine.faces.top();
        let lt = engine.thunk(left.ty, env);
        let rt = engine.thunk(right.ty, env);
        let l = engine.thunk(left.body, env);
        let r = engine.thunk(right.body, env);
        if !engine.conv(lt, rt, None, face)? {
            return Err(Error::plain("benchmark definitions have different types"));
        }
        let start = Instant::now();
        let equal = engine.conv(l, r, Some(lt), face)?;
        let elapsed = start.elapsed();
        Ok((elapsed, engine.statistics(), equal))
    }
}
