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
lake build leanervm-bench                   # compiles every transitive module to C, then links
.lake/build/bin/leanervm-bench 100          # iteration counts at 100% (the default), every group
.lake/build/bin/leanervm-bench 100 sumcheck # one group: `arith`, `sumcheck` or `provers`
.lake/build/bin/leanervm-bench 1 provers GKR # the prover workloads whose name contains `GKR`
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

### Sumcheck provers

The `sumcheck` group computes the honest prover's message of every round once, at the log-sizes
`4, 6, 8, 12, 16, 20` up to `LEANERVM_BENCH_MAXLOG` (default `20`), and the specification's
algorithm, assembled in the bench from functions no `@[csimp]` theorem replaces (`Sumcheck.claim`,
`ProductSum.coef0`, …), at `4, 6, 8` ("spec" lines). The fast and the specification's lines print
the same checksums at the same size.

| Workload | Prover |
| --- | --- |
| `interpolate 4 nodes over E` | `CLagrange.interpolate` of a cubic at the table sumcheck's nodes |
| `Sumcheck.plain 2^n x 3 tables` | `Sumcheck.roundPoly` with unit weights, summand `t₀ · t₁ · t₂`, nodes `0, 1, y, y + 1` |
| `Sumcheck.normalized 2^n x 3 tables` | the same with the weights of `eq(p, ·)` |
| `ProductSum 2^n` | `ProductSum.roundPoly`, WHIR's product sumcheck of two tables |
| `TableSumcheck 2^n rows x 4 columns` | the table sumcheck's rounds on one table of `2 ^ n` rows, four columns, three constraints of degree two and one push form |

The fast paths are `Sumcheck.roundPoly_eq_roundPolyFolded`,
`ProductSum.roundPoly_eq_roundPolyFolded`, `TableSumcheck.formula_eq_formulaFast`,
`CMvPolynomial.eval₂_eq_eval₂Fast` and `SumcheckRound.evaluate_eq_evaluateHorner` (see
`docs/architecture.md`). Recorded on 2026-10-22 on the same machine, shared with other builds; "before" is `6ebb3f2`, the same bench source
compiled against the library without these fast paths, where the fast and the specification's
lines run the same algorithm. Total milliseconds for all `n` rounds:

| Workload | `n` | Before (ms) | After (ms) | Speedup |
| --- | ---: | ---: | ---: | ---: |
| `Sumcheck.plain` | 8 | 3,187 | 37 | 87x |
| `Sumcheck.plain` | 12 | 783,379 | 857 | 910x |
| `Sumcheck.plain` | 16 | about 2 · 10^8 (extrapolated) | 17,177 | about 10^4 |
| `Sumcheck.plain` | 20 | about 5 · 10^10 (extrapolated) | 323,329 | about 10^5 |
| `Sumcheck.normalized` | 8 | 3,290 | 42 | 79x |
| `Sumcheck.normalized` | 12 | 735,646 | 863 | 850x |
| `Sumcheck.normalized` | 16 | about 2 · 10^8 (extrapolated) | 19,171 | about 10^4 |
| `Sumcheck.normalized` | 20 | about 5 · 10^10 (extrapolated) | 356,405 | about 10^5 |
| `ProductSum` | 8 | 3,208 | 19 | 165x |
| `ProductSum` | 12 | 768,698 | 406 | 1,900x |
| `ProductSum` | 16 | about 2 · 10^8 (extrapolated) | 9,198 | about 2 · 10^4 |
| `ProductSum` | 20 | about 5 · 10^10 (extrapolated) | 180,584 | about 3 · 10^5 |
| `TableSumcheck` | 8 | 12,454 | 253 | 49x |
| `TableSumcheck` | 12 | 3,693,962 | 5,471 | 680x |
| `TableSumcheck` | 16 | about 9 · 10^8 (extrapolated) | 129,736 | about 7 · 10^3 |
| `TableSumcheck` | 20 | about 2 · 10^11 (extrapolated) | 2,613,272 | about 10^5 |

"Before" at `n = 16, 20` is extrapolated from `n = 12` by the factor `4` per variable its
algorithm takes (every point of every next claim evaluates every table, `2 ^ n` work each, at
`2 ^ (n - j - 1)` points); at `n = 12` it took 13 minutes for the plain sumcheck and an hour for
the table sumcheck, with the same checksums as "after". The interpolation, twelve inverses through
a field dictionary, takes 0.18 ms a round and is left as is.

A round message is a function of the context and the challenges, so each round binds its tables
afresh: `m · 2 ^ n` work per round, `n · m · 2 ^ n` over the sumcheck instead of `m · 2 ^ n`, which
dominates the plain sumcheck at `2 ^ 20`. The rest is `E` arithmetic, about 3 µs a product (see
above). The table sumcheck adds per point the formula: the weight of each table's coordinates,
`τ_max` products, and its row polynomials; and per round the columns read off the stack through
the layout (`Layout.readWith`, `μ` comparisons a cell).

### The honest provers' tables

The `provers` group times, once each, the tables the honest provers of the bus phase and of the
grand-product argument build, and the stack of a leanISA witness. A third argument keeps only the
workloads whose name contains it (`.lake/build/bin/leanervm-bench 1 provers "GKR"`).

| Workload | Computation |
| --- | --- |
| `lagrangeBasis 2^16`, `2^20` | `lagrangeBasis` at a random `E` point; the checksum is the basis' sum, `1` |
| `stackOf leanISA 2^μ cells` | `LeanIsa.stackOf` of the constraint statement tests' hand-built witness (`fillW 1 g memCnt`) at its sizes, the memory log-size raised, at the BLAKE2s `FlockSpec` |
| `stackOf's Flock region, 2^3 compressions` | that stack's `QFLOCK` column alone: `F.gen` of the witness's eight `BLAKE2S` rows |
| `bus leaves leanISA 2^μ_bus` | the three sides' `Bus.sideLeaves` of the leanISA instance at those sizes, on a random stack |
| `column read leanISA 2^k cells` | one memory column read off that stack (`M3Instance.column`, through the layout) |
| `cube point and index …` | the cube point of an index and back, on 22 coordinates, generic and over `E`: most of a cell read |
| `GKR last layer 3 trees 2^μ` | the `μ - 2` sumcheck messages and the children of the grand-product argument's last radix-four step, on three random trees |

The fast paths are the `@[csimp]` theorems listed in `docs/architecture.md`, "Performance backend
contract". Recorded on 2026-10-23 on the same machine as above, shared with other builds; "before"
is `6ebb3f2`, the same bench source compiled against the library without these fast paths. Each
"before" and "after" pair printed the same checksum.

| Workload | Before | After |
| --- | ---: | ---: |
| `lagrangeBasis 2^16` | 3.47 s | 0.32 s |
| `lagrangeBasis 2^20` | 78.8 s | 4.85 s |
| `stackOf leanISA 2^15 cells` | over 900 s (stopped) | 3.11 s |
| `stackOf leanISA 2^18 cells` | not run | 3.20 s |
| `stackOf's Flock region, 2^3 compressions` | same code | 3.02 s |
| `bus leaves leanISA 2^8` | 810 s | 0.32 s |
| `bus leaves leanISA 2^12`, `2^16`, `2^20` | not run | 0.35 s, 0.66 s, 5.94 s |
| `column read leanISA 2^11 cells` | 0.171 s | 0.0015 s |
| `column read leanISA 2^19 cells` | not run | 0.42 s |
| `cube point and index, generic` / `over E`, `2^19` | not run | 2.83 s / 0.42 s |
| `GKR last layer 3 trees 2^8` | 1.86 s | 0.037 s |
| `GKR last layer 3 trees 2^12` | 532 s | 1.00 s |
| `GKR last layer 3 trees 2^16`, `2^20` | not run | 18.5 s, 394 s |
| `evalMle 2^16 E-table` (above) | 0.56 s | 0.30 s |

The stack costs its Flock region, `F.gen` of the `BLAKE2S` rows (about 0.38 s a compression, the
circuit's trace on bitsets of `2^14` bits); the rest is linear and small. A cell read is a cube
point lifted through the layout and decoded, about 0.8 µs at 22 coordinates. A step of the
grand-product argument from layer `m` costs `m` rounds of `O(2^(m+2))` work: the honest prover
keeps no state between messages, so every round rebuilds its trees' level below, and in the bus
phase the leaves. `E` products, about 3 µs each, dominate every row of this table.

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
