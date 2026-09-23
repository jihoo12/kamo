# Kamo

An experimental Cartesian cubical proof-assistant kernel in Rust. It uses safe
indexed arenas and explicit S-expressions. There are no postulates, recursive
definitions, or special evaluator cases for a library function named `ua`.

`examples/univalence.kamo` contains **checked definitions** of equivalences,
`ua`, identity and Boolean-negation equivalences, and the full `univalence`
theorem: the canonical map from universe paths to equivalences is an equivalence.
The implementation is a new kernel, not a formally verified or independently
audited implementation of the metatheory.

## Run

```sh
cargo build --release
scripts/with-limits.sh target/release/kamo check examples/univalence.kamo
scripts/with-limits.sh target/release/kamo normalize examples/univalence.kamo neg-true
# false
scripts/with-limits.sh target/release/kamo normalize examples/univalence.kamo neg-false
# true
scripts/with-limits.sh target/release/kamo normalize examples/univalence.kamo neg-inverse
# false
scripts/with-limits.sh target/release/kamo normalize examples/univalence.kamo neg-twice
# true
```

`--stats` on `normalize` reports evaluator work, arena allocations, and retained
arena capacity. `--reference` disables interning, reduction caches, and the
optimized collapsing of substitution suspensions. Both modes use the same
mathematical reduction rules; this is a differential implementation check, not
an independent proof of correctness.

## Resource limits

The development runner imposes a **512 MiB virtual-address-space limit** and a
30-second timeout on the child process. These are Linux/Bash process limits,
independent of the checker. It requires `timeout` from GNU coreutils.

The library and CLI additionally enforce:

- 4 MiB input limit and 512 levels of source-expression nesting.
- By default, 1,000,000 evaluation/checking steps and 250,000 arena nodes per
  declaration or normalization, configurable with `--fuel` and `--max-nodes`.
- Bounded face-solver depth, intermediate expansion, clause size, and caching.
- A fresh semantic arena for each checked declaration, discarded immediately
  afterwards. Normalization also uses its own arena and compacts unreachable
  semantic nodes between quotation tasks.

A resource error is an **inconclusive check**, never a successful proof or a
judgment that a mathematical statement is false. Node limits are work/storage
guards, not a hard byte limit; use the runner for a hard process limit. Syntax
is retained for the lifetime of a checked program. Arena statistics exclude
hash maps, transient solver allocations, allocator metadata, and stack space;
use OS peak RSS measurements for total process memory.

## Language

Definitions are ordered and explicit: `(def name type body)`. Later definitions
can refer to earlier ones. `;` starts a line comment. Functions, pairs, and paths
are checked against an expected type; use `(ann term type)` when their type must
be inferred, for example before applying an inline lambda.

| Form | Meaning |
| --- | --- |
| `(U level)` | Explicit, non-cumulative universe; `U n : U (n+1)` |
| `(Pi x A B)`, `(lam x body)`, `(app f x)` | Dependent function, introduction, application |
| `(Sigma x A B)`, `(pair a b)`, `(fst p)`, `(snd p)` | Dependent pair and projections |
| `Bool`, `true`, `false` | Strict Booleans |
| `(bool-elim motive true-case false-case value)` | Dependent Boolean elimination |
| `Nat`, `zero`, `(suc n)` | Strict natural numbers |
| `(nat-elim motive zero-case step value)` | Dependent natural elimination; step takes predecessor and recursive result |
| `(Path i A left right)`, `(path i body)`, `(at p r)` | Dependent paths and interval application |
| `(coe i A r s cap)` | Transport from `r` to `s` in family `A` |
| `(com i A r s cap ((face tube) ...))` | Heterogeneous composition; each tube binds `i` |
| `(system A ((face value) ...))` | A compatible system covering the current face |
| `(Glue B ((face A equivalence) ...))` | Equivalence extension of `B` |
| `(glue G base ((face value) ...))` | Introduction with explicit Glue type `G` |
| `(unglue G value)` | Projection with explicit Glue type `G` |

Dimensions are `0`, `1`, or bound interval names. Faces are `top`, `bottom`,
`(= r s)`, `(and phi psi)`, or `(or phi psi)`. Interval variables have a separate
namespace from term variables. They are **not Boolean variables**: the faces
`i = 0` and `i = 1` do not cover an arbitrary interval.

Formation checks, tube/cap compatibility, overlaps, and endpoint equations are
mandatory. Each Glue equivalence contains a forward function and a proof that
all its homotopy fibers are contractible; providing an inverse function alone
does not suffice.

## Library API

```rust
use kamo::CheckedProgram;
let program = CheckedProgram::check("(def answer Bool true)")?;
assert_eq!(program.normalize("answer")?.text, "true");
# Ok::<(), kamo::Error>(())
```

`CheckedProgram` owns immutable checked syntax. Its constructors check all
definitions; the public API does not expose unchecked evaluator entry points or
semantic arena IDs. Results own their output strings and statistics and survive
arena disposal. `Options` exposes the work/node budgets and evaluation mode.
`benchmark_conversion` times semantic conversion without parsing, type checking,
quotation, or output in the timed section.

## Tests and benchmarks

```sh
CARGO_BUILD_JOBS=1 cargo test --no-run
scripts/with-limits.sh cargo test --lib --tests -- --test-threads=1
CARGO_BUILD_JOBS=1 cargo bench --bench kernel --no-run
scripts/with-limits.sh cargo bench --bench kernel
```

The benchmark uses five fresh evaluator sessions per case and reports median
conversion time plus arena counters. Cases cover repeated univalence transport,
transport through dependent functions and pairs, nested Glue, and open-term
conversion. See [benchmark notes](docs/benchmarks.md) for measured results and
their limitations.

The first milestone omits Agda compatibility, implicit inference, general
recursion, user-defined inductives, higher inductive types, and editor tooling.
Universe levels are explicit numbers; the checked library supplies its theorem
at `U 0` with the necessary `U 1` auxiliaries rather than universe polymorphism.
Pretty printing produces explicit normal forms with generated binder names;
some introduction forms still need annotations when reused as inference inputs.

See [rule correspondence](docs/rules.md) for the theory, evaluator, and trusted
implementation boundary.

Quotation uses an explicit work stack for all terms and face formulas, with no
structural depth cap. `--max-output-bytes` bounds the UTF-8 output (default 16 MiB),
and `--max-quote-tasks` bounds pending tasks (default 250,000). Every quotation
task consumes the shared `--fuel` budget. Evaluation still has recursive code;
iterative quotation does not establish stack safety of the whole evaluator.
Failures report emitted bytes, pending tasks, and steps; partial output is not
returned as a normal form. See [full normalization measurements](docs/normalization.md).
See the [kernel audit and remediation](docs/kernel-audit.md) for the conversion
and stack-exhaustion regressions.

The [evaluator memory investigation](docs/evaluator-memory.md) records allocation
profiles, compaction/sharing changes, and the still-incomplete full-univalence
normalization runs. `normalize-dag FILE NAME` fully reduces into a shared text
graph; `--max-output-bytes` then bounds shared storage. It reports exact expanded
size only after the traversal succeeds.
