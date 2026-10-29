# Benchmarks

The initial benchmark suite measures repository engineering performance rather than VM
execution performance:

- a clean `lake build`;
- a warm repeat of the same build; and
- the `lake test` path.

The `Build timing` workflow records each measurement as JSON Lines, preserves the command
logs, and publishes a compact table in the GitHub job summary. Treat the numbers as CI-runner
observations, not stable machine-independent performance claims.

Runtime benchmark groups belong here once leanerVM has executable semantics. Each such group
must name the workload, parameter revision, expected result, and whether it measures Lean code
or a native boundary. Smoke tests must not be presented as performance benchmarks.

Runtime reports should compare applicable implementations on the same workload: the pure Lean
reference, Lean's native/C-compiled executable, Rust leanVM, optimized Rust FFI or CUDA kernels,
and code emitted by a future domain-specific compiler. Report compilation, initialization,
transfer, and steady-state execution separately, and pair every optimized path with a behavioral
differential check.

For Rust aggregation, record whether initialization used `setup_prover` with its process-wide
arena or `setup_prover_without_arena` with the system allocator. Do not compare timings or peak
memory across those modes without labelling the difference. Current upstream ARM and x86 results
are useful context, not a substitute for measurements on the hardware and source revision named
by a leanerVM benchmark.

Once the corresponding semantics exist, versioned target workloads should include opcode mixes,
BLAKE2s batches, XMSS-only aggregation, SPHINCS-only aggregation, mixed aggregation, and recursive
aggregation. Match public inputs and workload parameters across implementations; do not copy
upstream headline numbers into an evergreen benchmark assertion.

## Column-weight evaluator

`lake build novelBasisBench` builds a local native/C microbenchmark of the column-weight
`Weight.mle` route. Run `.lake/build/bin/novelBasisBench SAMPLES SEED` (defaults 32 and 20261028).
It compares a separately assembled reference product with the public column-weight route at
`(κ,R)=(0,1),(1,1),(8,2),(22,1)`; the last is a deployed WHIR level shape. Inputs vary per
iteration, and matching output checksums are required. Timed intervals cover point construction,
weight construction and evaluation; they do not construct the exponentially large cube table.
One `IO.Ref` allocation per batch forces the checksum before the second timer read. Inspect
the emitted C before interpreting timings: a pure `let` can be floated past that read. The
checksums are non-injective sample controls; universal correctness comes from the Lean equality.

`.lake/build/bin/novelBasisBench startup` performs module initialization only. Measure its
external wall/user-CPU time separately. The inverse cache contains per-root thunks: import
allocates those thunks, while a stage's inverse is computed and cached when first queried.
`first KAPPA RATE SEED` measures a fresh process's first public-route result before reference
checks or warmup, then checks its complete field value. `check SAMPLES SEED` compares every
full field result at kappa 0, 1, 2, 8, 22, 64 and 65; it prints all three limbs for comparisons
between source variants. Default timed batches are warmed. None of these modes equates a
checksum with complete equality. The default proof-library gate does not build this non-default
executable: explicitly run `lake build novelBasisBench` and its modes when changing this path.
Comparisons must use identical benchmark source, seed, sample count, compiler and dependency
pins; retain both native binaries, their hashes, generated C and the first-use/startup records.

This is a local evaluator workload, not end-to-end verifier latency, a Rust comparison or a
machine-independent speed claim. A warmed paired benchmark on a shared host is not a controlled
cold-build benchmark. The reference implementation deliberately bypasses the `columnWeightMle`
compiler substitution, so equality checks do not compare the fast path with itself.
