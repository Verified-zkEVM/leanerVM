# Benchmarks

The initial benchmark suite measures repository engineering performance rather than VM
execution performance:

- a clean `lake build`;
- a warm repeat of the same build; and
- the `lake test` path.

The `Build timing` workflow records each measurement as JSON Lines, preserves the command
logs, and publishes a compact table in the GitHub job summary. Treat the numbers as CI-runner
observations, not stable machine-independent performance claims.

## `leanervm-bench`: compiled arithmetic and hashing

`bench/LeanerVMBench.lean` is the `leanervm-bench` executable. It measures steady-state
nanoseconds per operation of Lean code compiled to C by Lean's own compiler; there is no native
boundary. Build and run it with

```sh
lake build leanervm-bench          # compiles every transitive module to C, then links
.lake/build/bin/leanervm-bench 100 # iteration counts at 100% (the default)
```

Inputs come from a xorshift seeded by `LEANERVM_BENCH_SEED` (default `12345`), so nothing is
evaluated at compile time, and each line ends with a checksum: two builds that print the same
checksums at the same seed and percentage computed the same values. Setup (building tables and
leaves) is outside the timed interval.

| Workload | Operation |
| --- | --- |
| `K mul`, `K inv` | `a * b`, `(a + b)⁻¹` on `K` |
| `K mul on words` | `FastBF64.mulWord` on `UInt64`, without the conversions |
| `E add`, `E mul`, `E inv` | `a + b`, `a * b`, `(a + b)⁻¹` on `E`, through the instances a monomorphic call site names |
| `E inv (Field dictionary)` | `x⁻¹` through a `Field E` dictionary, as generic code such as interpolation reaches it |
| `BLAKE2s 64 B`, `512 B` | `Blake2sHash.blake2sBytes` |
| `Merkle root 2^12 rows x 8 K` | `merkleRoot` of 4096 leaves of eight `K` words |
| `evalMle 2^16 E-table` | `CMlPolynomialEval.evalMle` of a 2^16-entry `E` table at an `E` point |

The fast paths are the `@[csimp]` theorems of `LeanerVM.Parameters.ToCompPoly.BF64Fast`,
`LeanerVM.Parameters.ToCompPoly.ExtensionFast`, `LeanerVM.Semantics.Blake2sFast` and
`LeanerVM.Protocol.Blake2sHashFast` (see `docs/architecture.md`, "Performance backend
contract"). Recorded on 2026-10-22 on a QEMU virtual CPU without `pclmulqdq`, 32 cores, one
thread; "before" is `a37b2b0`, the same bench source (less the two workloads added later)
compiled against the library without the fast paths, run at 1% of the iteration counts; the
checksums of both runs agree at 1%.

| Workload | Before (ns/op) | After (ns/op) | Speedup |
| --- | ---: | ---: | ---: |
| `K mul` | 25,235 | 177 | 142x |
| `K inv` | 1,874,466 | 1,376 | 1,360x |
| `K mul on words` | n/a | 75 | n/a |
| `E add` | 363 | 489 | unchanged code; a rerun of "before" gave 491 |
| `E mul` | 424,513 | 3,163 | 134x |
| `E inv` (not the production path) | 163,419,743 | 1,110,615 | 147x |
| `E inv (Field dictionary)` | same path as `E inv` | 18,208 | about 9,000x |
| `BLAKE2s 64 B` | 72,239 | 1,406 | 51x |
| `BLAKE2s 512 B` | 587,110 | 10,840 | 54x |
| `Merkle root 2^12 rows x 8 K` | 635,838,800 | 18,701,567 | 34x |
| `evalMle 2^16 E-table` | 59,858,789,990 | 568,452,830 | 105x |

The `E inv` row is a monomorphic `x⁻¹ : E`, which names the ring-level `Ext.instInv` and
keeps the exponentiation `x ^ (q^3 - 2)`. No library code takes that path: every `E` inverse in
the library is generic in its field (`Protocol/ToCompPoly/Interpolation.lean`,
`Arithmetization/Tables/Jump.lean`) and so reaches Cramer's rule, the `Field dictionary` row. The
fast field structures also carry fast integer powers (`zpowFast`); their rational casts and
scalar products (`nnratCast`, `ratCast`, `nnqsmul`, `qsmul`) stay those of the original instances,
over the specification's multiplication: correct, and slow.

"After" ran at 100%. The machine was shared with other builds, and single numbers moved by up to
a third between runs; read the table as orders of magnitude. The two BLAKE2s rows and the Merkle
row were measured again on 2026-10-23 (median of three runs), after `compressFast` moved its
working words into the fields of a structure, which compiled code keeps unboxed, and the hashers
read blocks in place and leaves as words; the previous binary, run alternately in the same session,
gave 2,921 ns, 31,484 ns and 33,300,309 ns for them, and the checksums agree. `K mul on words`
includes the loop's boxing of the accumulator.

Each `K` element is a `BitVec 64`, a natural number at run time, so an element with its top bit
set is a heap-allocated big integer; converting to and from a machine word costs more than the
product on words itself (`K mul on words`). `E` is three such limbs. A faster carrier needs
CompPoly to store a `BF64` as a `UInt64`, which changes a definition and is out of this suite's
scope.

Further runtime benchmark groups belong here once leanerVM has executable semantics. Each such
group must name the workload, parameter revision, expected result, and whether it measures Lean code
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
