# Full normalization experiment — 2026-09-22

Quotation now uses explicit tasks for every term constructor, type-directed eta
expansion, face formula, and binder scope. It writes once into a bounded String;
there is no recursive quotation call and no 64-level depth cap. The evaluator
called by quotation still contains recursive operations. This change does not
claim global stack safety or a proof of normalization.

The library `Options` and CLI expose:

- `max_output_bytes` / `--max-output-bytes`: maximum materialized UTF-8 bytes,
  default 16 MiB. This bounds output length, not total process memory.
- `max_quote_tasks` / `--max-quote-tasks`: maximum pending quotation tasks,
  default 250,000. Binder entry/exit and face printing use these tasks too.
- `fuel` / `--fuel`: shared evaluation and quotation work budget. Each task
  consumes fuel, including text emission and scope changes.
- `max_nodes` / `--max-nodes`: existing semantic arena node budget.

Allocation failures for the output/work buffers return errors. Error diagnostics
include the number of bytes already emitted internally, remaining tasks, and
steps. Incomplete output is discarded, never returned as a valid normal form.

## Explicit full-univalence runs

All runs below actually invoked `normalize ... univalence`, not just `check` or
normalization of a transport example. They used the release build, one process
at a time, a 30-second timeout, and hard virtual-memory caps. Output was redirected
to files. The files are empty because normalization failed before returning its
owned output. Logs preserve the partial-buffer counts.

| Node budget | Fuel | Hard memory cap | Emitted bytes before failure | Pending tasks | Steps | Peak RSS (KiB) | Seconds | Outcome |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 4,000,000 | 4,000,000 | 2 GiB | 676,765 | 271 | 2,445,087 | 975,480 | 1.71 | Node budget exhausted |
| 12,000,000 | 40,000,000 | 4 GiB | 1,847,754 | 265 | 6,978,231 | 3,207,720 | 6.12 | Node budget exhausted |
| 24,000,000 | 100,000,000 | 8 GiB | 3,614,127 | 217 | 13,769,260 | 6,347,452 | 12.47 | Node budget exhausted |

The first run used the default 16 MiB output / 250,000 pending-task limits; the
other runs used 64 MiB / 1,000,000. All three returned a normal error exit (1),
not a stack overflow, timeout, or OS allocation abort. Fuel, output, and pending
work budgets were not exhausted.

**Full normalization has not completed.** The next observed limit is explicitly
the arena node budget. Retention of intermediate values, environments,
substitutions, and caches makes this evaluator memory-intensive: the largest
run retained roughly 6.1 GiB RSS while building only about 3.4 MiB of output.
This is evidence of an implementation cost, not evidence that the normal form
itself is intrinsically too large. Its complete size and completion time remain
unknown; these prefixes do not justify extrapolating either. No recursive
evaluator crash was observed in these runs, but larger/different inputs may
still expose one. Raising budgets further on a 32 GiB machine is not a substitute
for investigating retention and repeated evaluation.

## Reproduce

```sh
CARGO_BUILD_JOBS=1 cargo build --release
bash audits/2026-09-22/run-univalence.sh
```

The runner preserves exact stderr/time logs and exit statuses and disables core
dumps. It requires GNU time; set `KAMO_TIME` if `/usr/bin/time` is unavailable.
The original measurements used `/run/current-system/sw/bin/time`.

## Regression validation

Tests cover the former 30,000-successor crash, nested pair quotation beyond the
old cap on a 2 MiB worker stack in both modes, exact output-byte limits, pending
work limits, and binder scope in rechecked eliminator output. The public audit
runner additionally rechecks open function/pair transport and computed Glue
normal forms and their definitional equality with the originals. These tests
validate quotation cases; they are not evidence of completed normalization of
the full theorem.
