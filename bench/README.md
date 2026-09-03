# Benchmarks

The initial benchmark suite measures repository engineering performance rather than VM
execution performance:

- a clean `lake build --wfail`;
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
