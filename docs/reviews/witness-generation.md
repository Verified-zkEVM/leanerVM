# Review: the verified witness generator and completeness from an execution (#192)

Branch `feat/witness-generator` (#192), written on `main` after #185 (`25da57d32`) on 2026-11-05,
with `main` at `6439d8878` merged in (`48695ccba`); adversarially reviewed on 2026-11-12 in three
areas (the statements, the random-oracle grind bound, the evidence and documentation), the
findings met on the branch. Pin: leanVM `a386121f`. It claims T2 for the padded trace
(`witnessGen_correct`) and the completeness half of T4 (`proveExecution_complete`,
`proveExecution_rom_complete`); no soundness statement changes, and no definition a soundness
headline mentions. `#print axioms` gives the kernel's three axioms for every public theorem whose
statement or proof changed.

## The work under review

The completeness headline no longer says "a witness exists". leanVM's honest prover from an
execution is one computable function,

```
proveExecution fuel prog input t ρ  :=  witnessGen prog input t  >>=  prove fuel prog input · ρ
```

and three theorems are proved about it:

- **`proveExecution_rom_complete`** (random-oracle model). If `prog` is well-formed bytecode, `t` is
  a valid execution of `prog` on `input` whose stack fits (`StackFits prog t`, a condition on the
  trace's sizes, which implies that `t` fits the caps), and `ρ` is a valid rate, then the honest
  run (generate, prove with every hash a query to a random function, verify with the same
  function) is rejected with probability at most `(N+1)(1 − 2^-17)^min(fuel, 2^64) + N²/2^256`,
  `N = 264,246,250 + 6·fuel` (a proved bound on the prover's hash queries); at fuel `2^24`, at
  most `2^-154`.
- **`proveExecution_complete`** (deployed BLAKE2s). For well-formed bytecode and a valid execution
  that fits, every proof `proveExecution` returns is accepted by `verify`, and it returns none only
  if the stack does not fit, the rate is invalid, or a proof-of-work grind runs out of fuel; on a
  stack that does not fit it does return none (`proveExecution_eq_none_of_not_stackFits`).
- **`verify_proveChecked`** (no hypothesis). `proveChecked` first runs the proved checks of the
  hypotheses of the random-oracle form, in milliseconds to a fraction of a second, and returns none
  if one fails; every proof it returns is accepted, and under the hypotheses it is
  `proveExecution` (`proveChecked_eq`).

The hypotheses are decided by proved checks: `wellFormedB`, `checkTrace`, `stackFitsB` and
`validRate`, together `checkExecution_eq_true_iff`, after constant-time bounds on the memory, the
bytecode and the steps that a stack that fits implies (`StackFits.bounds`, `StackFits.steps_le`);
`Trace.Fits` follows from `StackFits` (`StackFits.fits`), and `fitsBy` decides it on a valid
execution for the bench. A test discharges every hypothesis of the random-oracle headline in the
kernel on a small program, so the theorem is not vacuous. The stack condition is exact: it fails
from `t.κ ≥ 25` (`not_stackFits_of_le`) and holds for `t.κ ≤ 24` with at most `2^16` steps and
`2^25` bytecode slots (`StackFits.of_short`).

### What changed in the statement

Before: `∀ valid t, ∃ w, SatisfiedBy w ∧ … prove w …`, with `w` built from classical choices
(`gLog?` through `MemImage.read`, the fill-block positions from a `Prop`). That says a fixed
prover succeeds on some input nobody can compute; it is silent on whether an honest party can
produce `w`. After: `w` is `witnessGen prog input t`, a closed term, so the prover's whole input
is `(prog, input, t)`. The private witness of an NP statement is still needed, here the execution
`t` (the committed memory image), and no theorem could avoid that: finding an execution is an NP
search (a guest that checks a signature, say), infeasible in general.

### Why there is no efficiency hypothesis

1. **The prover is a fixed program, not an existential.** A completeness theorem about a named
   computable term cannot hide an expensive search in a choice; its cost is a property of that
   term, measured like the verifier's.
2. **The discrete log is not hard.** `gLog?` only asks for an index below `2^κ ≤ 2^32`, and the
   memory the prover commits to has `2^κ` cells, so a table of powers is linear in the witness
   (the Rust's `GPow` is such a table). Independently, `g` has order
   `2^64 − 1 = 3·5·17·257·641·65537·6700417` (checked in `Parameters/Generator.lean`), smooth, so
   even an unbounded log costs a few thousand multiplications (Pohlig–Hellman with baby-step
   giant-step in each prime-order subgroup). `gLog?` is unchanged; the generator reads memory
   through a checked guess: a table lookup proposes an index `i`, accepted only if `g^i = a` and
   `i < 2^κ`, else an exhaustive scan runs. `addressIndexBy_eq_gLog` proves the reader equal to
   `gLog?` for every table, so the table needs no proof.
3. **Asymptotic polynomial time would be vacuous here.** `κ ≤ 32`, at most `6·2^32` steps, fixed
   parameters: every computable function is polynomial time at a fixed size. The meaningful
   notion is concrete cost, which is measured (below).
4. **The one probabilistic cost is the grind**, the proof-of-work nonce search in Fiat–Shamir. At
   BLAKE2s, whether a nonce below `fuel` exists on a given run is a fact about one deterministic
   computation and cannot be proved; in the random-oracle model a grind fails with probability
   `(1 − 2^-17)^fuel` (`fuel` capped at the `2^64` distinct nonces), and
   `proveExecution_rom_complete` bounds the run's failure with a proved count of the prover's
   queries.

### How the generator was built and verified

- **Reuse of the existence proof.** The old proof was already parametric: the fill-block starts
  and the `JUMP` table height were used only through their specifications. Its body became
  `padWitness_complete`, taking them as arguments; the generator searches them (`fillStarts`,
  `jumpHeight`) and proves the specifications. The rows and tables are built by the existing
  definitions through a reader argument, equal to the originals by `rfl` or by short private
  congruence lemmas (`padWitnessBy_eq` and its neighbours), so no constraint proof was redone.
- **The run** is stepped once, forward (`runSkelsBy`), proved equal to the reference `runSkels`
  on a valid execution; read counters are threaded through hash maps with equality lemmas.
- **Trusted code untouched.** No edit to `Semantics/{Memory,Instruction,Step,Execution}.lean` or
  to the statements of `SatisfiedBy`, `AssignmentRepresents`, `ValidExecution`, `Trace.Fits`,
  `WellFormedBytecode`. `Semantics.zeroDigest`, the compression of the all-zero cells that the
  padding's `BLAKE2S` frame holds, is now computed (`compressOut`) instead of chosen; its
  specification `zeroDigest_spec` is unchanged.

### Clean

Clean's witness-generation IR was surveyed at the pin and on Clean's `main`. Its per-row
generator (`Circuit.witgen`, proved to produce local witnesses) applies, but only `JUMP` has local
witnesses, and they are computed directly. Its ensemble generator is unverified and does not fit
leanVM: routing a row to its table needs the index of `pc` (a discrete log) or a program-specific
guard listing every `pc`; read counters are global state, not a function of one row; the
multiplicity cells are summed in `K`, which has characteristic 2; and its padding repeats one row
per table, while leanVM pads by running distinct closed walks (the fill blocks). Clean's open PR
#480 (`generate_complete`) needs a prime field with `2·#interactions < char`. So the generator
lives in leanerVM; no pin move was needed. Run on leanISA's ensemble, Clean's generator stops at
the first pushed state with `ambiguousDemand`, since all six tables accept it; the docstring of
`opcodeGeneration` and the leanISA blueprint's row, which said it would put a row in every table,
are corrected on the branch.

### Evidence on real programs

19 programs executed by the Rust executor at `a386121f` (`field_div`, `hash_chain_8`, the 15
`lean_compiler` test programs, Fibonacci 1000 and 20000) are checked in
(`tests/vectors/executions/`, `scripts/dump-execution-rust.sh`), and an XMSS aggregation guest
(`2^19`-slot bytecode) is regenerable with `-g`. On all of them `leanervm-witgen` finds the proved
hypothesis checks true and `witnessGen`'s table heights equal to the Rust's (the guest's differ
only by the Rust's committed-size floor); generation takes 0.2–0.7 s (Fibonacci 20000: 0.6 s;
the guest 1.5–1.9 s). The `Executables` workflow runs `leanervm-witgen --gen` on the 19 files and
`leanervm-prove execution`. `field_div` was proved end to end once (the Rust execution, the Lean
generator, the Lean prover, and the Lean verifier accepting; the proof took 290 s). The Lean
prover takes 84 s on the one-step trace of `leanervm-prove execution` (2026-11-12; the four
recorded runs since 2026-11-05 took 83 to 143 s). Every timing here is a single run on a shared
machine (`bench/README.md`).

### Limits

- The proof represents a padded execution: the same steps, the memory doubled with the fill frames
  above the image, where the Rust places them in free memory. Hence `StackFits` fails from
  `t.κ ≥ 25`; a witness shaped like the Rust's fails from `t.κ ≥ 26`.
- At BLAKE2s the grind is heuristic; the bound is in the random-oracle model.
- Agreement with the Rust is testing (heights, main rows), not proof; Rust-side facts are read
  from leanVM `a386121f`.
- The Lean prover is slow (minutes) though the generator is fast.

## Open questions

1. **The memory layout, a decision for the user.** `padTrace t pcs` has memory log-size `t.κ + 1`
   with the 48 fill frames at `2^κ + 12c` (`Semantics/PaddedImage.lean`, `frameBase`); the Rust
   places them at `max(2^16, next_free)` inside the same memory when there is room
   (`cpu/filler.rs`). Consequences: the memory block is twice the Rust's (`2^18` against `2^17`
   rows on every vector); `StackFits` fails from `t.κ ≥ 25`, where a witness of the Rust's layout
   fails from `t.κ ≥ 26`; and `Trace.Fits.room` (`t.κ < 32`) is a hypothesis only because of the
   doubling. A fix: pad at the first frame base above every cell the run reads (computable from
   the forward pass), keep `κ` when the frames fit, and replace `PaddedFrom` in the headline by
   "the same steps, and the images agree on every cell the run reads" (which still implies the
   same run). It changes a headline statement, so it waits for the user's decision; the branch
   does not change the layout.
2. **The Rust contracts lane is pinned to another leanVM revision.**
   `scripts/test-rust-contracts.py`, `Semantics/TraceInput.lean` and `RustExport.lean` cite
   `48a90420`; everything else, the execution vectors included, is at `a386121f`, and the
   interpreter changed between them (new hints `ResolveDeref`, `FrameAddress`, `AllocFrames`;
   layout and table edits). Re-pinning that lane, or moving every pin together under the
   dependency drift review, is a change of its own.
3. **Clean upstream.** Clean's verified ensemble generation does not cover a VM shaped like leanVM
   (above). A comment on Clean #480 could propose multiplicities safe in characteristic 2
   (exponents of `g`, as leanVM uses) and a demand mode for preallocated blocks, with leanerVM's
   generator as a worked example of the shape needed.

The items the built work owes (a committed-size floor, the program hash on large bytecode, the
fill-block search on large bytecode, a column-by-column comparison with the Rust's witness, the
prover's speed, and the grind bound counted per grind) are in
[protocol-status.md](../roadmap/protocol-status.md), in #192's *on merge* paragraph and under
*Also owed*.

## Findings of the adversarial review, and their disposition

The review found no theorem wrong or vacuous and no change to a soundness statement; its findings
were about a redundant hypothesis, a guard that could exhaust memory, the audit surface, generic
code in leanVM files, and the documentation and evidence.

| Finding | Disposition |
| --- | --- |
| `Trace.Fits` is implied by `StackFits`, so the random-oracle headline carried a redundant hypothesis | Fixed (`20c7a4601`): `StackFits.fits`; `hfit` dropped from `proveExecution_rom_complete`, its `_default`, `proveChecked_eq` and `stackFits_iff`; `checkExecution` no longer runs `fitsB` |
| The guarded prover could build a table of up to `2^32` powers before rejecting | Fixed (`20c7a4601`): `checkExecution` and `stackFitsB` test the constant-time bounds `StackFits.bounds` first, `fitsB` tests `t.κ < maxLogMem` first; regression tests at `t.κ = 25` |
| About 35 proof-only declarations of the generator and its checks public | Fixed (`b84d51c18`, `20c7a4601`): private; the stack material moved to `Protocol/LeanIsa/ExecutionStack.lean`, the constraint-form random-oracle completeness to `Protocol/HonestGame.lean` |
| The two completeness headlines stated the stack condition two ways | Fixed (`20c7a4601`): `proveExecution_complete` states it as `StackFits` |
| Duplicated reference code (`rowOfBy`, `limbsBy`, `cellBy`) and a doubled name | `opTableOf` renamed `opTableFrom`; the copies stay, proved equal by private lemmas (removing them redefines `rowOf` and `MemImage.limbsAt` low in the tree) |
| `Executable.lean`'s list of trusted statements stale | Fixed (`b84d51c18`) |
| The grind bound's audit surface (72 public declarations in `Prove/Queries.lean`, 46 in `Prove/Hom.lean`) | Fixed (`4cb6ea299`): 11 and 2 public; `Prove.pubLength_of_algebra`, `VerifierQueries.isTotalQueryBound_hashQuery` and `Verify.positionsWith_hom` stay public, each used by another file |
| `nonempty_of_sampleable` duplicated VCVio's `SampleableType.nonempty` | Fixed (`4cb6ea299`): deleted |
| The replay lemma restated VCVio vocabulary in the wrong file | Fixed (`4cb6ea299`): `evalWithAnswerFn_eq_of_mem_support_randomOracle`, over any `OracleSpec`, in `ToVCVio/RandomOracleReplay.lean` |
| Generic lemmas in leanVM files | Fixed (`4cb6ea299`, moved again in `d2b8496fa` and `7ba5599af`): the Merkle tree lemmas in `ToVCVio/Merkle.lean`, `Vector.mapM_hom` in `ToVCVio/MonadRel.lean`, the generic query bounds in `ToVCVio/QueryBound.lean` and `ToVCVio/MerkleQueries.lean` |
| Flexible `simp` calls; wording | Fixed (`4cb6ea299`, `b84d51c18`) |
| No CI built `leanervm-witgen`, ran `leanervm-prove execution`, or read the execution vectors | Fixed (`a9ad13991` and the documentation commit): both run in the `Executables` workflow; `docs/ci.md`, `docs/development.md`, `tests/vectors/README.md` |
| The status page rewrote #185's *on merge* paragraph | Fixed (documentation commit): #185's paragraph restored, #192's own paragraph and row added |
| Owed items that #192 builds still listed as owed | Fixed (documentation commit): the honest query bound, the random-oracle grind bound, the fixed fuel, `checkSatisfiedBy` for the vectors, and the T2 row of `leanvm-target.md`; the per-grind bound and a deployed rate stay owed |
| This file was an author's report with unposted issue drafts and scratch citations | Fixed (documentation commit): this archive; the drafts moved to the status page and the open questions above; the bound at fuel `2^24` is `2^-156.2` (the per-grind form `2^-182.1` at `L = 6`), not `2^-155.6`; the prover's times stated once |
| `docs/development.md`, `docs/leanisa-checker.md`, `bench/README.md` out of date | Fixed (documentation commit) |
| Lines over 100 columns | Fixed in every line the branch adds |

### Second round

A second review of the fixed branch found no theorem wrong or vacuous; its findings in the
statements, the grind bound and the evidence:

| Finding | Disposition |
| --- | --- |
| The guard did not bound `t.steps`: a trace announcing many steps of a run that never halts was stepped to the end before it was rejected | Fixed (`ab3b8f06a`): `StackFits.steps_le` (`t.steps ≤ 2^25` on a run whose stack fits); `checkExecution` and `stackFitsB` test it in their constant-time first check; a test rejects a trace announcing `2^40` steps at once |
| The rate was checked last, after the run | Fixed (`ab3b8f06a`): `validRate` is in `checkExecution`'s constant-time first check |
| `fitsB` and `fitsB_eq_true_iff` had no caller and the documents presented `fitsB` as the check | Fixed (`64bcd75a5`): deleted; the documents say that `StackFits` implies `Trace.Fits` and that `fitsBy` is the bench's check |
| "`proveExecution` returns none from `t.κ ≥ 25`" was prose only | Fixed (`ab3b8f06a`): `proveExecution_eq_none_of_not_stackFits`, cited in both docstrings |
| "Below `2^-154`" for a `≤` bound; "it is not" for a stack that does not fit | Fixed (`ab3b8f06a`) in `Headline.lean` |
| The generator's row writers and table builders, and the run checker's table-of-powers helpers, public | Fixed (`64bcd75a5`): 25 private; `witnessGen`, `mkRowsH`, `opRowsBy`, `powTable` and `runToHalt` keep public signatures, bodies not exposed |
| `docs/ci.md`'s workflow row stale; no step timeout on the two new `Executables` steps | Fixed (`788f46b96`): the row names `leanervm-witgen` and both steps; `timeout 900` and `timeout 300` |
| `leanervm-witgen` with no file exited `0`; the dump script's `--offline` undocumented; two line ranges off at the pin | Fixed (`788f46b96`): exit `2` with a usage line; the prerequisite in the script and `scripts/README.md`; `hash_chain.rs:20-58`, `:75-82`, `py_source.rs:22-52` |
| The prover's timings stated three ways | Fixed (documentation commit): four recorded runs, 83 to 143 s |
| A private copy of VCVio's `isTotalQueryBound_listMapM_const` | Fixed (`7ba5599af`): deleted; `isTotalQueryBound_vector_mapM` uses VCVio's |
| `ProofOfWork.lean`'s potential argument public | Fixed (`7ba5599af`): 17 more private; public are `PowSearch`, `Counted`, `Exhausted`, `prEvent_exhausted_le` |
| `Vector.mapM_hom` and `exists_isTotalQueryBound` away from their vocabulary | Fixed (`d2b8496fa`, `7ba5599af`): `ToVCVio/MonadRel.lean` and the new `ToVCVio/QueryBound.lean` |
| `Prove/Queries.lean` slow to elaborate | Fixed (`2054eae67`): `queryGrade` irreducible in `writeProof_grade` alone, and one count rewritten so unification does not run the prover; the file from 26 s to 12 s |
| Unused and internal-only `RunCodecHom` lemmas; wording in `HonestGame.lean` and `grindSearch` | Fixed (`531b400ed`, `5a9d419ec`): `map_gkr_of` deleted, three run lemmas private; "at most `2^-154`"; tags named |
