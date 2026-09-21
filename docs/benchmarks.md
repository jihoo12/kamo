# Benchmark baseline

Measured in this workspace on 2026-09-21 with Rust 1.95.0, using Cargo's default
release profile. These are local microbenchmarks, not a comparison with Agda,
`cctt`, or another proof assistant. The CSV contains the full results:
[benchmark-results.csv](benchmark-results.csv).

Each conversion uses a fresh evaluation session; times are medians of five runs.
Parsing, checking the declarations, printing, and quoting normal forms are outside
the timed region. Arena counters describe the entire session, including its small
type-comparison setup. They count allocated arena nodes and retained capacities,
not system allocator calls or total resident memory.

| Case | Shared/cached mode | Reference mode | Shared arena capacity | Reference arena capacity |
| --- | ---: | ---: | ---: | ---: |
| 32 successive univalence transports | 542 µs | 190 µs | 371 KiB | 674 KiB |
| Reuse a 32-transport result 16 times | 573 µs | 2,955 µs | 630 KiB | 10,784 KiB |
| Dependent function transport | 40 µs | 20 µs | 23 KiB | 71 KiB |
| Eight nested Glue types | 630 µs | 286 µs | 561 KiB | 734 KiB |
| Open conversion | 44 µs | 13 µs | 50 KiB | 47 KiB |

The shared mode is about **5.2× faster** and uses about **17× less arena capacity**
on the reuse workload. It is slower on these small, mostly linear computations:
interning and cache overhead outweigh saved evaluation. It remains the default
because sharing bounds repeated work, but this baseline does not establish it as
universally fastest. Selective caching and cheaper representations remain useful
future optimization targets. Nothing in the kernel recognizes the benchmark
names or special-cases the Boolean-negation equivalence.

The full checked library, including the `univalence` theorem, took approximately
0.02 seconds with **11,876 KiB peak RSS** in an OS-level measurement. The full
benchmark executable peaked at **16,332 KiB RSS**. Both ran under the development
runner's 512 MiB address-space cap and 30-second timeout. These measurements are
for the supplied workloads, not upper bounds for arbitrary inputs.

Reproduce:

```sh
CARGO_BUILD_JOBS=1 cargo build --release
CARGO_BUILD_JOBS=1 cargo bench --bench kernel --no-run
scripts/with-limits.sh cargo bench --bench kernel
scripts/with-limits.sh /usr/bin/time -v target/release/kamo check examples/univalence.kamo
```

Use the path to GNU `time` installed on your system; this environment provides it
at `/run/current-system/sw/bin/time`. For measuring only the benchmark process's
RSS, run the executable path printed by `cargo bench --no-run` directly under
`time`. The CSV is deliberately not a CI speed threshold: sub-millisecond timings
vary with hardware, load, compiler, and allocator behavior.

The reference evaluator is useful on the computation benchmarks but can exceed
the default node budget while checking the entire proof library. The benchmark
checks declarations in shared mode before comparing evaluation modes. The public
API likewise allows `CheckedProgram::check` followed by `normalize_with` using
`optimized: false`.
