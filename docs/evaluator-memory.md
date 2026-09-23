# Evaluator memory investigation (ongoing)

Full normalization of `univalence` has **not yet completed**. These measurements
are of that declaration itself. Checking it, or computing Boolean transports,
is not substituted for full normalization. The complete expanded size remains
unknown. Prefix sizes and explicit resource failures do not prove inherent
impracticality.

## What allocated and retained memory

The initial 4,000,000-node failure had 2,694,249 values, 312,649 environments,
and 973,087 substitutions. Of the values, 1,338,408 were substitution suspensions
and 616,267 were syntax suspensions. Arena lifetimes retained intermediate
objects long after quotation consumed them. Untrimmed environments retained
unused arguments; pushing the same substitution repeatedly reconstructed values
and freshened binders again. Captured source offsets near the final theorem's
arguments and `decode-section` dominated the original trace.

After those problems were reduced, the hot source expressions moved to the
`equiv-total-contr` pair/Glue construction (offsets 6067 and 6085), `reverse1`'s
path application (16060), and `id-equiv`'s fiber center (545 and 561). Later
prefixes also repeatedly unfold `decode` and `decode-retraction`. These are
checked library terms, not primitive univalence calls.

A further retention bug was in cache rooting: constant evaluations under many
obsolete faces kept those face contexts alive. Face IDs now participate in weak
cache removal. Memoized support summaries survive compaction if their values
survive; summaries contain semantic levels, not arena IDs.

## Implemented changes

- Trim closure environments to source free-variable slots; evaluate variables
  and literals without an extra syntax suspension.
- Memoize substitution pushing and native equivalence/fiber type construction.
- Skip provably irrelevant substitutions. Unknown support conservatively falls
  back to ordinary substitution. Preserve a binder's level only when the entire
  substitution cannot map or capture it.
- Compact values, environments, substitutions, and faces between quotation tasks.
  Pending terms, their types/faces, retained readback entries, and quotation's
  typed variable contexts are explicit roots. Persistent declarations still
  contain syntax only. Reference mode does not compact or use these shortcuts.
- Keep ordinary evaluation caches weak: surviving keys alone do not keep all
  previously computed graphs alive. An experiment retaining transitively reached
  cached heads pinned too much memory and was removed. A bounded expensive-head
  experiment also did not reduce work on the comparison workload and was removed.
- Memoize completed compound readback results. Keys include interpreted variable
  contexts, types, and faces. Canonical type heads avoid misses caused by delayed
  type suspensions. Larger completed subterms have reserved cache space.
- For known support, project irrelevant dimensions out of memoization's face key
  using exact equality partitions, preserving transitive equalities and distinct
  endpoints. Unknown support keeps the original key.
- Reuse quotation variables only for an identical domain, outer term/dimension
  context, and face. Reusing a term level merely by lexical depth is not safe.

No computation rule or library proof was replaced, and no axiom was added.

## Measurements retained so far

Raw profiles and exit logs are in `audits/2026-09-22/evaluator/`. The dates in
that directory identify the investigation's start. Seconds are elapsed command
measurements, including checking/profiling; some exploratory runs overlapped.
They are not controlled kernel-only speedup claims. RSS includes hash tables
and output buffers, unlike `Statistics::arena_bytes`.

| Build/experiment | Computed prefix bytes | Steps | Peak RSS KiB | Result |
| --- | ---: | ---: | ---: | --- |
| Initial evaluator | 676,765 | 2,445,087 | 975,480 | 4M node budget |
| Initial evaluator, larger arena | 3,614,127 | 13,769,260 | 6,347,452 | 24M node budget |
| Compact arenas, canonical compositions | 67,108,861 | 70,268,952 | 256,684 | Output budget |
| Weak face retention, larger readback cache | 67,108,864 | 64,829,892 | 158,792 | Output budget |
| Compound readback memoization | 67,108,422 | 18,656,438 | 163,792 | Output budget |
| Typed keys and larger-result retention | 67,108,422 | 12,389,441 | 170,648 | Output budget |
| Full traversal, older shared-output build | 1,551,383,468 | 1,000,000,000 | 192,548 | Fuel budget |
| Full traversal, compound shared-output build | 4,089,142,317 | 1,000,000,000 | 274,492 | Fuel budget |

The last shared-output run allocated 443,439,700 values cumulatively but retained
41,106 at its final sample, with 2,464 collections. Its incomplete output graph
had 699,228 nodes; 3,611,786,888 expanded bytes were replayed from completed
readback entries. Arena accumulation has been substantially reduced, but work
still repeats. This is not a completed normal form.

One earlier collector experiment panicked during a longer run. Root handling was
revised, with remapping assertions and regression tests. Subsequent traversals
passed that prefix and ran to explicit fuel/output limits. The old failure log
is retained rather than presented as a successful run.

## Shared output and independent size evidence

`kamo normalize-dag FILE NAME` runs the same full quotation rules but interns
completed output fragments in an owned acyclic graph. Successful output contains
only text and concatenation nodes, no evaluator values, suspensions, or deferred
normalization. `root ... expanded-bytes ...` gives its exact expanded UTF-8 size.
`--max-output-bytes` bounds this mode's shared storage, not expanded text. The
ordinary `normalize` command still produces expanded S-expression text.

The library provides `normalize_dag_with`, `NormalDag::encode`, and bounded,
iterative `NormalDag::materialize`. Tests compare its expansion byte-for-byte
with ordinary output in optimized and reference modes. A failed traversal never
returns a graph as a completed normal form.

The separate exact S-expression interning analyzer `analyze-prefix.rs` found
7,452,357 completed list occurrences but only 43,294 distinct lists in a 64 MiB
prefix, including an identical 830,505-byte subtree repeated ten times. Counts
for nested repeated subtrees overlap and must not be added as independent bytes.
This demonstrates duplication, but does not determine the complete output size.

## Reproduction

```sh
CARGO_BUILD_JOBS=1 cargo build --release
KAMO_PROFILE=1 KAMO_MEMORY_KIB=1572864 KAMO_TIMEOUT=600s \
  scripts/with-limits.sh /run/current-system/sw/bin/time -f 'time=%e rss=%M exit=%x' \
  target/release/kamo normalize-dag examples/univalence.kamo univalence \
  --max-nodes 4000000 --fuel 1000000000 --max-output-bytes 536870912 --stats \
  > /tmp/univalence.dag 2> /tmp/univalence-profile.log
```

Use a hard memory cap on profiling runs. `KAMO_PROFILE_PREFIX=PATH` optionally
saves an explicitly incomplete diagnostic text prefix after a quotation error;
it is not a successful result. Profiling records fresh allocation caller sites,
source offsets, cumulative allocations, retained node kinds, and progress.
