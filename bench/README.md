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
.lake/build/bin/leanervm-bench 1 runs        # provers run through ArkLib's `Prover.run`
.lake/build/bin/leanervm-bench 1 protocol pub 15 # leanVM's phases up to the public input
.lake/build/bin/leanervm-bench 1 flockpieces 15  # the cached Flock prover's pieces
.lake/build/bin/leanervm-bench 1 whir 16 1 spec  # WHIR's opening at mu = 16, rate 1/2
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

The ", with state" lines run the cached prover's messages (`Sumcheck.roundFromCache`,
`Sumcheck.stepCache`): the tables read off the context once and bound one challenge at a time,
`m · 2 ^ n` over the sumcheck. Recorded on 2026-10-23 on the same machine, beside the lines above,
each pair printing the same checksum (milliseconds for all `n` rounds):

| Workload | `n` | Stateless (ms) | With state (ms) |
| --- | ---: | ---: | ---: |
| `Sumcheck.plain` | 12 | 696 | 309 |
| `Sumcheck.plain` | 16 | 16,381 | 5,637 |
| `Sumcheck.normalized` | 12 | 825 | 431 |
| `Sumcheck.normalized` | 16 | 18,128 | 7,340 |
| `TableSumcheck` | 12 | 2,503 | 1,933 |
| `TableSumcheck` | 16 | 49,611 | 37,076 |

What is left is the round polynomial itself, `(d + 1) · 2 ^ (n - j - 1)` evaluations of the
summand at round `j`; in the table sumcheck the formula dominates.

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
| `GKR last layer 3 trees 2^μ, with state` | the same from the cached prover's data: the trees' levels built once (`Gkr.treesOf`), the children of the level below bound one challenge at a time (`Gkr.roundFromBound`, `Gkr.stepChildren`) |
| `Flock circuit: compile`, `one block, on words`, `on bitsets` | `ProductCircuit.compile` of the BLAKE2s circuit, and one compression's block traced on 64-bit words (`Compiled.traceW`) and on bitsets (`trace`) |

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

With prover state and the BLAKE2s column traced on words (`Blake2sFlock.genColumnFast`, through
`Blake2sFlock.genColumn_eq_genColumnFast`), recorded on 2026-10-23, each pair printing the same
checksum:

| Workload | Stateless | With state |
| --- | ---: | ---: |
| `GKR last layer 3 trees 2^8` | 0.040 s | 0.025 s |
| `GKR last layer 3 trees 2^12` | 0.93 s | 0.39 s |
| `GKR last layer 3 trees 2^16` | 19.2 s | 6.5 s |
| `GKR last layer 3 trees 2^20` | 382 s | 106 s |
| `Flock circuit: one block`, bitsets / words | 0.36 s | 0.18 s |
| `stackOf leanISA 2^15 cells`, steady | 3.0 s | 0.87 s |

The BLAKE2s circuit's forms are dense (about 3,000 of the `2^14` positions each, 89 million in
all), so the compiled circuit holds each form as its 256 words; compiling takes 3.5 s, once per
process (the first stack pays it). The last layer's messages are now the round polynomial's own
`O(nside · 2^ρ · (2^ρ + 1) · 2^(m - j))` products at round `j`.

### The honest provers, run

The `runs` and `protocol` groups run provers through ArkLib's `Prover.run`, the challenges drawn
by `IO.rand` from the seed (`runProver`), so that two provers timed at the same seed draw the
same challenges. `runs` times trivial sumcheck rounds and a plain sumcheck of three tables, with
state (`Sumcheck.cachedWeighted`) and without. `protocol` builds the leanISA stack of the
constraint statement tests' witness at memory log-size `lm + 1` (fourth argument, default `15`,
the smallest admissible: `2^19` cells, `2^17` bus leaves, `τ_max = 3` since the witness's opcode
tables are small, eight `BLAKE2S` rows), then runs the phases of `leanVmPhases` one after the
other, each on the output of the one before, up to the phase the third argument names (`bus`,
`table`, `pub`, `flock`, or `whole` for every phase and `leanVmFastProver`): the bus phase and
the table sumcheck with state (`Bus.busCached`, `TableSumcheck.tableCached`), beside their
stateless honest provers when the fifth argument is `spec`.

```sh
.lake/build/bin/leanervm-bench 1 runs
.lake/build/bin/leanervm-bench 1 protocol table 0 spec   # 2^15 cells, 2^8 leaves
.lake/build/bin/leanervm-bench 1 protocol pub 15         # the smallest admissible size
```

ArkLib builds an appended schedule's challenge samplers with `Fin.fappend₂`, which, compiled,
evaluates the inner schedules' entries at every step: `Prover.run` of `SumcheckRound.rounds`, a
schedule appended on the right once per round, took 0.6 ms at 4 rounds, 1.3 s at 7, 18 s at 8 and
261 s at 9. With the lazy instances of `LeanerVM.Protocol.ToArkLib.AppendLazy` it takes 0.5 ms at
8 rounds and 1.8 ms at 32. The plain sumcheck of three tables of `2^16` entries runs in 6.0 s with
state and 38.1 s without (the stateless prover also computes each message twice, once to send it
and once for its output statement). Recorded on 2026-10-23, each pair printing the same checksum:

| Phase | `2^15` cells, `2^8` leaves: stateless | with state | `2^19` cells, `2^17` leaves: with state |
| --- | ---: | ---: | ---: |
| the stack (`stackOf`) | | 3.9 s | 3.9 s |
| bus phase | 121 s | 0.35 s | 9.1 s (and 0.55 s to read its output) |
| table sumcheck | 7.2 s | 3.3 s | 4.1 s |
| public input | | 0.1 ms | 0.1 ms |
| Flock phase | | not finished in 15 min | not run |

The bus phase's output reads each block's selector weight; before
`Blocks.selectorWeight_eq_selectorWeightFast` each weight built a Lagrange basis of up to `2^17`
entries to read one, and reading the output took 64 s at the smallest size.

The Flock phase did not finish: the BLAKE2s inhabitant's R1CS carried the naive walks of
`ProductCircuit.toBlockR1CS` (`2^28` products a walk), and `Flock.leftTable` walks a block once
per entry it reads, in every round. The inhabitant's R1CS now walks the compiled circuit's words
(`ProductCircuit.toBlockR1CSE`, `LeanerVM.Protocol.FlockWalks`): the forward walk reads each row's
forms as 256 words each and, on a block of `0`s and `1`s, takes the parity of a form's AND with
the packed block; the backward walk scatters each row's entry onto its forms' set bits, the
entries' limbs as six half-words that an array holds unboxed. A first backward walk by columns
took 247 s (each column reads a bit of every row's form) and a scatter on boxed words 10 s. The
cached Flock prover (`Flock.flockCached`) walks each block once and builds its skip tables once
at `z_skip` and its lincheck tables once at `α`; the skip message, which combines every table at
each of the 64 coset nodes, adds the weights' subset sums a byte of tables at a time
(`Flock.combBytes_eq`). With these and the bus phase's output tabulated once (`Bus.memoOut`),
`leanervm-bench 1 protocol whole 15`, recorded on 2026-10-23 on the same machine, each phase's
checksum the same as in the run before the byte sums, where the Flock phase took 23.8 s and the
whole protocol 31.1 s:

| Phase, `2^19` cells, `2^17` leaves, `τ_max = 3`, `2^3` BLAKE2s blocks | With state |
| --- | ---: |
| the stack (`stackOf`) | 3.8 s |
| bus phase | 9.4 s |
| table sumcheck | 0.59 s (4.1 s before the output was tabulated) |
| public input | 0.1 ms |
| Flock phase | 16.6 s |
| opening | 1.18 s |
| whole protocol (`leanVmFastProver`, from the stack), warm | 25.3 s |
| the opening's batched weight's values (WHIR's input), 113 claims | 4.2 s (95.4 s before) |

The whole protocol runs last, in the process that ran the phases, so it finds the BLAKE2s circuit
compiled (3.5 s, which the stack pays) and the R1CS's row table built (3.1 s, which the Flock
phase's first walk pays): each is built once per process, and its 25.3 s leaves both out. The rows
above, the stack included, add up to 31.6 s.

The opening's prover never reads the batched weight's values; WHIR's prover does, at the start of
the commitment's opening. The weight combines 112 column claims and the switched claim. A column
claim's point is read through the layout, so its coordinates include the block's selector bits
and its equality kernel vanishes off the block: `eqBatch` combines the kernels coordinate by
coordinate, dropping a term on the half where its factor is zero (`Opening.weight_eq_weightFast`,
`@[csimp]`), and the switched claim's kernels likewise (`Flock.ringWeightFast`, in the cached
Flock prover). Built from the `2 ^ 19`-entry Lagrange bases, the column claims alone took 48.7 s.

`leanervm-bench 1 flockpieces 15` times the Flock prover's pieces once each on the same region:

| Piece | Time |
| --- | ---: |
| the witness tables | 0.10 s |
| a block's walk: first (builds the row table, every row's forms as words) / after | 3.28 s / 0.17 s |
| the walked products, eight blocks | 1.55 s |
| the skip message: by dot products / a byte of tables at a time | 11.2 s / 4.7 s |
| one skip table | 0.07 s |
| the backward walk | 5.0 s |
| the folded witness / the slices | 0.15 s / 0.05 s |
| the zerocheck's 11 messages / the lincheck's 8 | 0.28 s / 0.95 s |

What is left is linear in the circuit's 89 million nonzero entries: the row table, the forward
walks on words, and the backward walk, one `E` addition on half-words an entry.

Rust leanVM at the pin (`a386121f`, its release build, `leanvm fibonacci --n 1000 --tracing` with
`RAYON_NUM_THREADS=1`) proves its smallest run on the same machine in 3.5 s: memory `2^16`,
`2^19.06` committed cells, a different program from the bench's witness at the same sizes.
Execution and witness 16 ms, commitment 48 ms, bus 1.89 s (of which GKR 1.47 s), constraints
0.20 s, Flock reduction 0.35 s, PCS opening 1.00 s. The Lean prover is about five times slower in
the bus phase, three times in the table sumcheck and fifty times in the Flock phase.

### WHIR's opening

The `whir` group (`leanervm-bench 1 whir μ R [spec]`) commits a random table on `μ` variables at
rate `1/2^R` with the deployed parameters' levels (`Whir.ladder`): the level-0 word's rows by the
additive transform (`Whir.wordRows`), checked against `wordOf` at two rows, and their Merkle
root; then it runs WHIR's cached prover (`Whir.whirOpenCached`) on the equality kernel at a
random point, with the word's rows stored, through `Prover.run`, the honest prover of `whirOpen`
beside it when the fifth argument is `spec`, and the verifier on each transcript. The cached
prover binds the fold rounds' tables once per challenge, carries each level's folded table to its
messages, and encodes the next level's word once, its rows kept as data. `whiropen κ t` times
the first level's pieces at `μ = κ + 6`, and `whirpieces κ R` the transform's on `2^κ`
coefficients. Recorded on 2026-10-23 on the same machine, every
transcript accepted:

| Workload, rate `1/2`, 223 queries at the first level (224 at `μ = 19`) | `μ = 15` | `μ = 16` | `μ = 19` |
| --- | ---: | ---: | ---: |
| level-0 word by the transform | 0.40 s | 0.71 s | 7.1 s |
| level-0 Merkle root | 0.32 s | 0.60 s | 4.4 s |
| opening, with state (`whirOpenCached`) | 1.1 s | 2.2 s | 17.6 s |
| opening, honest (`whirOpen`) | 12.0 s | 25.7 s | not run |
| verifier on the transcript | 0.15 s | 0.17 s | 0.27 s |

Each line came from its own fix. Before them, at `μ = 19`: the word took 256 s, the opening
316 s and the verifier 272 s.

* The additive transform `fwd` reads each node's halves inside the closures that build the node's
  outputs, so compiled code rebuilt a half at every entry: 2.1 s for one coset of `2^13`
  coefficients over `E` and 2.0 s over `K`. `fwd_eq_fwdFast` (`@[csimp]`) reads them once, over
  any ring (0.17 s and 34 ms), and over `E` the transform runs as three transforms of the limbs'
  64-bit words, `xor` and `mulWord` (`Whir.encodeE`): 13 ms a limb, 87 ms a lane of `2^13`
  coefficients onto `2^14` positions.
* A word is a function in compiled code, and a closure returning one is expanded to take the
  position as one more argument: the next level's word, a message computed by a closure, was
  rebuilt at every row the queries and the verifier read (0.64 s a row at the second level of
  `μ = 19`). Its rows are now data, built when the step starts (`Whir.wordRows`).
* The query batch's weight takes `2^κ` products of `E` per column and `t` more per entry, on
  values in `K`; on words (`Whir.queryCubeW`, `queryWeight_eq_queryWeightFast`) it takes 0.97 s
  for 224 positions on `2^13` entries, 9.7 s before.
* The fold rounds and the first message run `E`'s products on the limbs' words
  (`ProductSum.roundCacheW`, `ExtWords.mulW`): 5.3 s for the six fold rounds on `2^19` entries,
  12.6 s through the field instances.
* Before `batchWeight_eq_batchWeightFast`, the combination by powers rebuilt every table at every
  entry: 213 s at `μ = 15`.

`μ = 19` is the size of the smallest leanVM stack (`2^19` cells); there Rust leanVM's commitment
takes 48 ms and its PCS opening 1.00 s on one thread. What is left at `μ = 19` is `E` arithmetic:
the fold rounds (5.3 s, of which most is converting limbs between bit vectors and words), the
level-0 word (7.1 s, 20 million word products and the vectors around them), and the Merkle
tree's leaves (4.4 s, each row's limbs listed and hashed).

## `leanervm-verify`: the verifier on the Rust proof

`bench/LeanerVMVerify.lean` is the `leanervm-verify` executable: `Verify.verify` compiled, on the
proof the pinned Rust prover makes of the division program of its test suite
(`scripts/dump-proof-rust.sh`; the fixture `tests/LeanerVMTests/Protocol/RustProofData.lean`).
Interpreted, one run takes over a minute, so the test module checks only the honest proof and the
mutations rejected before the chain walk passes its setup's reads; the executable runs the rest.

```sh
lake build leanervm-verify          # compiles every transitive module to C, then links
.lake/build/bin/leanervm-verify 5   # the checks, then five timed runs of `verify`
```

It prints the honest proof's verdict, then each mutation of
`LeanerVMTests.Protocol.Verify.mutations` with the stage that rejects it (`outcome`: the setup,
the openings' shapes, a read with the reader's error, or a phase of the algebra) against the
stage recorded for it, the same for the statement's mutations (`statementMutations`: the proof
of the fixture against a changed input or program), and WHIR's algebra on the honest transcript
with its mutations at every level (`whirChecks`); the exit code is `1` if any check fails. The
timed runs exclude the fixture's parsing.

Recorded on 2026-10-23 at the fixture of leanVM `a386121f` (770 scalars, four openings of 223,
56, 32 and 22 rows, a stack of `2^20` cells), on the machine of the table above: every check
passes, and `verify` takes 1.7 to 1.9 s a run over five runs (2.6 to 3.1 s before the compiled
fast paths of the bus output, the totals, the row folds and the lincheck terminal); on 2026-10-25,
after `fwd_eq_fwdFast`, 0.76 to 0.81 s, every check passing. A flipped
scalar of a phase is rejected by the next level's grinding check, since the chain moves; only the
last level's query message and tail rounds reach WHIR's terminal check through the stream. The
phases' own checks are exercised on the honest wire by the phase test modules and `whirChecks`.

## `leanervm-check`: one verdict per proof file

`bench/LeanerVMCheck.lean` is the `leanervm-check` executable: `Verify.verify` compiled, on proof
files in the dump format, one line per file with the verdict and the stage `outcomeAt` names, for
the differential tests against the pinned Rust verifier
([`tests/differential/`](../tests/differential/README.md)). The format of its lines is in
[the test vectors' guide](../tests/vectors/README.md).

```sh
lake build leanervm-check
.lake/build/bin/leanervm-check tests/vectors/fill.proof   # after gunzip -k; or: serve
```

## `leanervm-prove`: the honest prover

`bench/LeanerVMProve.lean` is the `leanervm-prove` executable: the honest non-interactive prover
(`LeanerVM.Protocol.Prove`) compiled, on the constraint statement tests' witness
(`fillW 1 g memCnt`, the executor's `mul_192bit_word` with its fill blocks), whose sizes are the
smallest admissible: memory `2^16`, a stack of `2^19` cells, `2^3` BLAKE2s blocks, three WHIR
levels at rate `1/2`. It runs the prover's writer in `IO` with the time read at each phase's first
squeeze, writes the proof in the dump format, reads it back, and checks it with `verify` and its
mutations (`mutationsOf`); with `pure` it also runs `prove` in `Id`.

```sh
lake build leanervm-prove
.lake/build/bin/leanervm-prove tests/vectors/fill.proof 1   # the proof, its checks, the times
.lake/build/bin/leanervm-prove probe 1                      # the commitment's steps, one by one
.lake/build/bin/leanervm-prove tamper tests/vectors/fill.proof  # four provers, one message changed
.lake/build/bin/leanervm-prove log tests/vectors/fill.proof     # the honest run, every hash logged
.lake/build/bin/leanervm-prove m3                           # M3Holds's clauses on the witness's stack
.lake/build/bin/leanervm-prove m3 9                         # the same at memory 2^10
```

`log` runs the prover once more with every hash logged (the run of `honestAdversary` with BLAKE2s
answering), then `verifyWith` on its proof with every hash logged, and checks that the proof is
the file's, that the verifier accepts it, and that the joint log has no collision and no hit
(`LeanerVMTests.Protocol.LogScan.scan`, one pass with hash maps, which the headline's tests check
against `QueryLog.HasCollision` and `Hit` on small logs): the decidable clauses of the headline's
hypothesis at `δ = 0`. The flip clause is not decidable. Then the extractor on the prover's log
(`extractChecks`): the level-0 word `extract` reads off it (`wordRows` under the proof's level-0
root) must be the committed word (`Whir.kwordRows` of the witness's stack), the commitment's list
decoder must read it as the witness's stack alone, and `extract` itself, which decides `M3Holds`
of the decoded stack last, must return the witness's sizes and stack: the leanVM-level witness of
acceptance tests 24 and 37, run, where `extract_honest` would state it. Recorded on 2026-10-25:
487250 prover queries (the grinding's candidates most of them) and 3291 verifier queries, three
roots; the proof is the vector's, `verify` accepts it, and the joint log has no collision and no
hit; the word read off the log (16384 rows, 2.8 s) is the committed word (recomputed in 2.5 s),
the decoder returns one stack, the witness's (13.9 s), and `extract` from the log returns the
witness's sizes and stack in 21.7 s. The two runs take 183 s, the scan 9 s, the whole check
4 min, 6.4 GB at the peak (the logged prover's).

Before `a53dc86` and `67c9a6d`, `extract` was not run at this size: the committed word took 231 s
and the decoder 250 s (the transform rebuilt each half at every entry of a step, quadratic in
its length; `fwd_eq_fwdFast`), and deciding `M3Holds` read each committed column of a boundary
block once per tuple, decided the bus's permutation by `List.decidablePerm`, quadratic in its
65698 tuples a side, and rebuilt each of the Flock region's 64 bit tables at every position it
read. A native run of `extract` was stopped after more than 10 minutes, and one on the empty log
grew to 40 GB and was killed. `m3` decides each clause
on the witness's stack, at its sizes or at memory `2^(lm + 1)`; compiled code now sorts the
tuples' keys (`M3Instance.instDecidableBalanced_eq`), reads each column once
(`M3Instance.boundaryTuples_eq_boundaryTuplesFast`, `M3Instance.instDecidableCountsNonzero_eq`)
and builds each bit table once (`BlockR1CS.instDecidableBatchHolds_eq`). Recorded on 2026-10-25,
one thread, 0.8 GB at the peak:

| `M3Holds` on the witness's stack | memory `2^10`, stack `2^15`: before | after | memory `2^16`, stack `2^19`: before | after |
| --- | ---: | ---: | ---: | ---: |
| the boundary's tuples, both sides | 3.8 s | 0.005 s | about 4 h (extrapolated, quadratic) | 0.42 s |
| `Balanced` (its tuples included) | 3.9 s | 0.17 s | not run | 1.1 s |
| `aux`, the Flock region's R1CS on `2^3` blocks | 32 s | 4.5 s | not run (the same region) | 4.5 s |
| `M3Holds`, after the clauses above | 33 s | 1.6 s | not run | 2.7 s |

`aux` includes, the first time, 3.3 s to build the BLAKE2s circuit's row table; the other clauses
take under 0.2 s. The bus has 1186 tuples a side at memory `2^10` and 65698 at `2^16`.

Beside the mutations of the proof, both `leanervm-prove` and `leanervm-verify` run the algebra on
the honest wire with one message changed in each front phase (a grand-product round coefficient
and a child value, a table round coefficient and column value, a public value and the number of
public values, a zerocheck and a lincheck round coefficient, a Flock slice; `frontChecksOf`) and
in WHIR (`whirChecksOf`), each rejected by its own phase. A mutation of the proof's stream cannot reach the front phases'
algebra, since the next grinding check rejects it first; `tamper` reaches it through the stream:
it runs the prover with one front phase's message changed as it is sent (`tamperOps`), so that
the chain moves, every later nonce is ground and every word opened at the moved positions, and
checks that the proof is read to its end and rejected by that phase's algebra. Recorded on
2026-10-23: the four proofs (a grand-product round coefficient, a table column value, a public
value, a Flock slice) are rejected at the bus phase, the table sumcheck, the public input and the
Flock phase, about 440 s each.

On the machine of the tables above, one thread: "before" recorded on 2026-10-23 (6.1 GB at the
peak), "after" on 2026-10-25, after `fwd_eq_fwdFast` (6.4 GB at the peak) but without the Flock and
WHIR provers on words, and "stack top" on 2026-10-25 at the top of the stack, with both (1.06 GB at
the peak):

| Phase | Before | After | Stack top |
| --- | ---: | ---: | ---: |
| the stack (`stackOf`) | 3.9 s | 4.1 s | 3.8 s |
| the commitment: the level-0 word's rows by the transform, the tree, the root | 228 s | 3.1 s | 3.2 s |
| bus phase (cached) | 9.0 s | 8.4 s | 8.4 s |
| table sumcheck (cached) | 0.44 s | 0.39 s | 0.38 s |
| public input | 6 ms | 6 ms | 6 ms |
| Flock phase (cached) | 16.6 s | 15.6 s | 16.3 s |
| the opening's batching and WHIR's first round polynomial | 129 s | 108 s | 7.7 s |
| WHIR's levels (cached), their commitments and grinding, the openings | 47 s | 41 s | 12.9 s |
| **the prover, from the witness** | **434 s** | **181 s** | **52.7 s** |
| `verify` on the proof | 1.36 s | 0.63 s | 0.62 s |

`prove` in `Id` takes 175 s (425 s before) and returns the same proof, byte for byte, and both
return the vector's. Of the commitment, the probe gives 2.4 s (228 s before) to the 64 lanes'
encodings by the additive transform over `K`, 0.04 s to the stored rows and 0.76 s to the Merkle
tree of `2^14` leaves. Before `fwd_eq_fwdFast` a step of the transform rebuilt each half of its
input at every entry it wrote. Rust leanVM at the pin proves its smallest run in 3.5 s on one
thread on the same machine, so the prover at the top of the stack is about 15 times slower (50
times without the provers on words), within the blueprint's one to two orders of magnitude; the
Flock phase and WHIR now dominate. Every mutation is rejected at the
stage it names.

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
