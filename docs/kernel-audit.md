# Kernel audit — 2026-09-21

Audited revision: `63c57cf5cb51a799049f5d933384de97ca9f3ea2`.
This records the original source review and bounded adversarial test pass, not a
proof of soundness or an independent external review. The original audit did not
change kernel behavior. Remediation is recorded below.

## Remediation status

Both findings have now been addressed:

- A1: removed shared-substitution cancellation. Both execution modes apply the
  substitution before comparing under the ambient face. Permanent regressions
  assert that the counterexample is unequal both before and after forcing.
- A2: successor chains are quoted iteratively into one output buffer. The original
  30,000-successor input now normalizes successfully. Other structural quotation
  has a fixed depth budget of 64, returning an explicit resource error. Regression
  tests run both modes on 2 MiB worker stacks, including a deep dependent-pair
  output that reaches the structural limit.

This does not claim that every recursive operation in the kernel is stack-safe.
The new depth limit applies to quotation; general evaluator/checker recursion
remains a separate hardening concern. The conservative limit may reject printing
otherwise valid, deeply nested terms, without invalidating their checked proofs.

Post-fix results are in `audits/2026-09-21/public-results-fixed.json` and
`audits/2026-09-21/internal-results-fixed.txt`. Historical result files are retained.
The runners now require the fixed behavior.

## Original findings

### A1 — Conversion cancels a substitution without preserving its face context

**Potential soundness issue; internal counterexample confirmed, source-level
reachability unresolved.** Location: `src/eval.rs:645`, in `Engine::same`.

The shortcut compares `Sub(v, s)` and `Sub(w, s)` by comparing `v` and `w` in the
*unchanged* face context. Equality under a face is preserved by substitution
only with the corresponding treatment of that face. Identical substitution IDs
alone do not establish that condition.

The internal reproducer uses a well-typed neutral
`p : Path k (U 0) Bool Bool`, distinct dimensions `i, j`, face `i = j`, and
`σ = [i := 0]`. It compares:

```
(p @ i)σ    and    (p @ j)σ
```

The shortcut discards σ and accepts `p @ i = p @ j` using the face. Forcing first
instead gives `Bool` and `p @ j`; the original face `i = j` does not imply
`j = 0`, and conversion rejects that comparison. The observed results are:

| Mode | Conversion before forcing | Conversion after forcing |
| --- | --- | --- |
| Shared/cached | equal | unequal |
| Reference | equal | unequal |

Removing only this shortcut in a disposable source copy makes both comparisons
return unequal in both modes. That experiment isolates the cause; it is not a
validated production patch.

**Reachability qualification:** the reproducer constructs semantic values using
private engine operations. Many checker-generated substitutions replace fresh
bound dimensions absent from the ambient face; the shortcut may be valid under
that stronger invariant. This audit did not find a checked source program that
violates that invariant or forges a proof. The implementation neither checks nor
documents the required invariant at this shortcut. Do not interpret this finding
as a demonstrated closed proof of `true = false`.

Recommended remediation: remove this cancellation, or enforce and test a precise
face-preservation precondition before using it. Add conversion-before/after-force
and substitution stability tests, including nontrivial face assumptions. Resolve
this before making a kernel soundness claim.

### A2 — A valid input aborts normalization through stack exhaustion

**Confirmed availability bug (P2).** Location: `src/quote.rs:135–137`, recursively
calling `quote_inner` for every natural-number successor. Related guard:
`src/quote.rs:35` counts work but not recursion depth.

A file containing these 30,001 shallow declarations is only 877,802 bytes:

```
(def n0 Nat zero)
(def n1 Nat (suc n0))
; Continue with one successor of the preceding definition.
(def n30000 Nat (suc n29999))
```

`kamo check` accepts it. Release-build `kamo normalize FILE n30000`, with default
fuel/node limits and the 512 MiB/30-second process wrapper, aborts with SIGABRT
and `thread 'main' ... has overflowed its stack`. The shell reports 134;
Python's subprocess interface reports -6. The parser's nesting bound does not
help because the source definitions are shallow while their unfolded value is
deep. This is a stack exhaustion reproduction, not evidence explaining the
user's earlier client OOM.

Recommended remediation: quote with an explicit work stack and output builder,
or introduce a conservative checked recursion limit throughout recursive kernel
operations. Return a resource-exhaustion error rather than aborting. Exercise the
public library on bounded-stack worker threads as well as the CLI. A recursive
String-building implementation also repeatedly copies the growing normal form.

## Checks performed

- Read the checker, delayed substitution/forcing/conversion, native Glue and
  universe expansions, face solver, public API, parser, arenas, and quotation.
  Cross-checked the principal computational rules against
  [ABCFHL §§2.7–2.14](https://www.cs.cmu.edu/~rwh/papers/ccctt/preprint.pdf).
- Existing suite: **36 tests passed**, including the checked univalence theorem,
  equivalence rejection, universe rejection, composition boundaries, and arena
  session isolation.
- Public audit probes: **16 rejection checks** (eight inputs in both modes), and
  **eight normalization/rechecking checks** (four inputs in both modes).
  Rechecking includes a constant path witnessing definitional equality between
  each original term and its printed normal form. Cases include open transports
  through functions and pairs and endpoint restriction of a computed Glue type.
- Independent face oracle: **97 generated formula entries**, all **9,409
  entailment pairs**, evaluated over **1,296 assignments** enumerating every
  equality partition of four dimensions and two distinct endpoints. Universal
  quantification was also checked for every formula and assignment. Passed.
  This finite test includes generic interval values; it does not treat the
  interval as Boolean.
- Internal conversion audit: **two failing assertions**, one per mode, recording
  A1. These were separate from the ordinary test suite at audit time; the fixed
  behavior is now also covered by permanent kernel regressions.
- Isolated public stress probe: reproduced A2 with OS memory/time caps. The
  reproduction script disables core dumps.

## Reproduction and artifacts

From the repository root:

```sh
CARGO_BUILD_JOBS=1 cargo build --release
python3 audits/2026-09-21/run-public.py
bash audits/2026-09-21/run-internal.sh
```

The internal runner compiles a temporary copy of the source and appends the
white-box tests there; it does not modify production files. Its expected exit
status on the audited revision is 101 because the two A1 assertions fail.
After remediation, the internal runner must exit 0, and the public runner asserts
that the formerly crashing input produces the complete expected normal form.

Artifacts:

- [Public runner](../audits/2026-09-21/run-public.py)
- [Recorded public results](../audits/2026-09-21/public-results.json)
- [Internal runner](../audits/2026-09-21/run-internal.sh)
- [Conversion reproducer](../audits/2026-09-21/substitution_tests.rs)
- [Independent face oracle](../audits/2026-09-21/face_tests.rs)

## Remaining assurance gaps

The reference mode shares conversion and mathematical reduction code with the
optimized mode; A1 demonstrates why their agreement is not an independent
soundness oracle. The native Glue/universe constructions have not been formally
verified by this audit, and passing a univalence theorem in this same kernel
cannot establish its soundness. No source-level false proof was found in the
reviewed cases. This does not rule one out.
