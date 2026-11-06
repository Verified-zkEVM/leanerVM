# A verified witness generator for leanVM, and completeness without an efficiency assumption

Branch `witgen-fv`, rebased onto `main` after #185 (`25da57d32`). Written 2026-11-05, rebased 2026-11-06.

## Result

The completeness headline no longer says "a witness exists". leanVM's honest prover from an
execution is now one computable function,

```
proveExecution fuel prog input t ρ  :=  witnessGen prog input t  >>=  prove fuel prog input · ρ
```

and three theorems are proved about it with the standard axioms only:

- **`proveExecution_rom_complete`** (random-oracle model). If `prog` is well-formed bytecode, `t`
  is a valid execution of `prog` on `input` that fits the caps and whose stack fits
  (`StackFits prog t`, a condition on the trace's sizes), and `ρ` is a valid rate, then the
  honest game — generate, prove with every hash a query to a
  random function, verify with the same function — is rejected with probability at most
  `(N+1)(1 − 2^-17)^min(fuel, 2^64) + N²/2^256`, `N = 264,246,250 + 6·fuel` (a proved bound on
  the prover's hash queries); at fuel `2^24`, below `2^-154`.
- **`proveExecution_complete`** (deployed BLAKE2s). For well-formed bytecode and a valid execution
  that fits, every proof
  `proveExecution` returns is accepted by `verify`, and it returns none only if the stack is
  too large, the rate is invalid, or a proof-of-work grind runs out of fuel.
- **`verify_proveChecked`** (no hypothesis at all). `proveChecked` first runs the proved checks of
  every hypothesis above (milliseconds to a fraction of a second) and returns none if one fails; every proof it returns is
  accepted, and under the hypotheses it is `proveExecution` (`proveChecked_eq`).

Every hypothesis is decided by a proved check (`wellFormedB`, `checkTrace`, `fitsB`,
`stackFitsB`, `validRate`; together `checkExecution_eq_true_iff`). All hold on every
Rust-executed program we exported, including a 2^19-slot XMSS aggregation guest. The theorem is
not vacuous: a test discharges every hypothesis of the random-oracle headline in the kernel on a
small program. The stack condition is exact: it fails from `t.κ ≥ 25` (`not_stackFits_of_le`)
and holds for `t.κ ≤ 24` with at most `2^16` steps and `2^25` bytecode slots
(`StackFits.of_short`).

## What changed in the statement, and why it matters

Before: `∀ valid t, ∃ w, SatisfiedBy w ∧ … prove w …`, with `w` built from classical choices
(`gLog?` through `MemImage.read`, the fill-block positions from a `Prop`). That says a fixed
prover succeeds *on some input nobody can compute*; it is silent on whether an honest party can
produce `w`. After: `w` is `witnessGen prog input t`, a closed term, so the prover's whole input
is `(prog, input, t)`. The private witness of an NP statement is still needed — here the
execution `t` (the committed memory image) — and no theorem could avoid that: finding an
execution is an NP search (think of a guest that checks a signature), infeasible in general.

## Why there is no efficiency hypothesis

1. **The prover is a fixed program, not an existential.** A completeness theorem about a named
   computable term cannot hide an expensive search in a choice; its cost is a property of that
   term, measured like the verifier's.
2. **The discrete log is not hard.** `gLog?` only asks for an index below `2^κ ≤ 2^32`, and the
   memory the prover commits to has `2^κ` cells, so a table of powers is linear in the witness
   (Rust's `GPow` is such a table). Independently, `g` has order `2^64 − 1 =
   3·5·17·257·641·65537·6700417` (checked in `Parameters/Generator.lean`), smooth, so even an
   unbounded log costs a few thousand multiplications (Pohlig–Hellman with baby-step
   giant-step in each prime-order subgroup). `gLog?` is unchanged; the generator reads memory through a
   *checked guess*: a table lookup proposes an index `i`, which is accepted only if `g^i = a`
   and `i < 2^κ`, else an exhaustive scan runs. `addressIndexBy_eq_gLog` proves the reader equal
   to `gLog?` for every table, so the table needs no proof.
3. **Asymptotic PPT would be vacuous here.** `κ ≤ 32`, at most `6·2^32` steps, fixed
   parameters: every computable function is "polynomial time" at fixed size. The meaningful
   notion is concrete cost, which we measure (below).
4. **The one probabilistic cost is the grind**, the proof-of-work nonce search in Fiat–Shamir.
   At BLAKE2s, whether a nonce below `fuel` exists on a given run is a fact about one
   deterministic computation and cannot be proved; in the random-oracle model it fails with
   probability `(1 − 2^-17)^fuel` per grind (`fuel` capped at the `2^64` distinct nonces). `proveExecution_rom_complete` bounds it, with a
   proved count of the prover's queries.

## How the generator was built and verified

- **Reuse of the existence proof.** The old proof was already parametric: the fill-block starts
  and the `JUMP` table height were used only through their specifications. Its body became
  `padWitness_complete`, taking them as arguments; the generator searches them
  (`fillStarts`, `jumpHeight`) and proves the specs. The rows and tables are built by the
  existing definitions through a reader argument, equal to the originals by `rfl` or by short
  congruence lemmas (`padWitnessBy_eq`), so no constraint proof was redone.
- **The run** is stepped once, forward (`runSkelsBy`), proved equal to the reference
  `runSkels` on a valid execution; read counters are threaded through hash maps with
  equality lemmas.
- **Trusted code untouched.** No edit to `Semantics/{Memory,Instruction,Step,Execution}.lean` or
  to the statements of `SatisfiedBy`, `AssignmentRepresents`, `ValidExecution`, `Trace.Fits`,
  `WellFormedBytecode`. `zeroDigest` (the BLAKE2s digest of zero, a completeness-only constant)
  is now computed instead of chosen.

## Clean

Clean's witness-generation IR was surveyed at the pin and on main. Its per-row generator
(`Circuit.witgen`, proved to produce local witnesses) applies, but only `JUMP` has local
witnesses, and they are computed directly. Its ensemble generator is unverified and does not fit
leanVM: routing a row to its table needs the index of `pc` (a discrete log) or a
program-specific guard listing every `pc`; read counters are global state, not a function of
one row; the multiplicity cells are summed in `K`, which has characteristic 2; and its padding
repeats one row per table, while leanVM pads by running distinct closed walks (the fill
blocks). Clean's open PR #480 (`generate_complete`) needs a prime field
with `2·#interactions < char`. So the generator lives in leanerVM; no pin move was needed.

## Evidence on real programs

19 programs executed by the Rust executor at `a386121f` (`field_div`, `hash_chain_8`, the
15 `lean_compiler` test programs, Fibonacci 1000 and 20000) plus an XMSS aggregation guest
(2^19-slot bytecode) are checked in or regenerable (`scripts/dump-execution-rust.sh`,
`leanervm-witgen`). On all of them: the proved hypothesis checks hold; `witnessGen`'s table
heights equal Rust's (the guest differs only by Rust's committed-size floor); generation takes
0.2–0.7 s (Fibonacci 20000: 0.6 s; guest 1.5–1.9 s). `field_div` was proved end to end
(Rust execution → Lean generator → Lean prover → Lean verifier accepts; prove 290 s).

## Limits

- The proof represents a *padded* execution: same steps, memory doubled with the fill frames
  above the image (Rust places them in free space). Hence `StackFits` fails from `t.κ ≥ 25`;
  a witness shaped like Rust's fails from `t.κ ≥ 26`.
- At BLAKE2s the grind is heuristic; the bound is in the random-oracle model.
- Agreement with Rust is testing (heights, main rows), not proof; Rust-side facts are read
  from leanVM `a386121f`.
- The Lean prover is slow (minutes) though the generator is fast.

Open problems with proposed fixes: the last section.

## Review of the task prompt

Points resolved without the author: the prover must be given the execution (finding one is
infeasible in general); "for every input there exists a prover" is trivial, the gap was `∃ w`; `gLog?` is a
bounded log; there are three sources of cost (log, padding search, grind) and only the grind is
probabilistic; Clean's IR is version-dependent; the base PR moved during the work.


## Open issues found by the witness-generation work (drafts, not posted)

Base: branch `witgen-fv` on `main` `25da57d32`. Each item: what is
wrong or missing, evidence, proposed fix, scope.

### 1. The generator doubles memory; Rust places the fill frames in free space
- **What.** `padTrace t pcs` has memory log-size `t.κ + 1` with the 48 fill frames at
  `2^κ + 12c` (`Semantics/PaddedImage.lean`, `frameBase`). Rust places them at
  `max(2^16, next_free)` inside the same memory when room exists (`cpu/filler.rs`, report 03).
- **Consequences.** (a) The memory block is twice Rust's (2^18 vs 2^17 rows on every vector);
  (b) `StackFits` fails from `t.κ ≥ 25`, where a Rust-shaped witness fails from `t.κ ≥ 26`; (c) `Trace.Fits.room`
  (`t.κ < 32`) is a hypothesis only because of the doubling.
- **Fix.** Pad at the first frame base above every cell the run reads (computable from the
  forward pass), keep `κ` when the frames fit; replace `PaddedFrom` in the headline by
  "same steps, and the images agree on every cell the run reads" (still implies the same run).
  Changes a headline statement — needs the reviewer's decision.

### 2. No committed-size floor in the generator
- **What.** The Rust recursion prover sets `min_log_committed = 22`, raising SET to 2^17 and
  JUMP accordingly (guest vector: Lean heights 2^[11,11,10,11,9,8] vs Rust 2^[11,11,17,11,11,8]).
- **Fix.** A `floor` parameter to `witnessGen` (padding tables to a floor is already the fill
  plan's job: `fillTarget n floor`), with `witnessGen_correct` generalised over it. Needed
  before the generator can reproduce recursion proofs (T6), not for the base headline.

### 3. `programHash` materialises a 64 MB `List UInt8`
- **What.** On the 2^19-slot guest, `programHash` takes 36 s and 3.1 GB; both `prove` and
  `verify` hash the program (report 12).
- **Fix.** Hash from a `ByteArray`/streaming BLAKE2s, proved equal to the list form.

### 4. The Rust contracts lane is pinned to a different leanVM revision
- **What.** `scripts/test-rust-contracts.py`, `Semantics/TraceInput.lean` and `RustExport.lean`
  cite `48a90420`; everything else (upstreams.json, FillPlan, Executable, the proof fixture, the
  new execution vectors) is `a386121f`. The interpreter changed between them (new hints
  `ResolveDeref`, `FrameAddress`, `AllocFrames`; layout/tables edits).
- **Fix.** Re-pin the contracts lane to `a386121f` (or bump everything together under the
  dependency drift review).

### 5. Wrong docstring about Clean's generator
- **What.** `opcodeGeneration` (`Arithmetization/Tables/Basic.lean:52-60`) and the blueprint row
  (`docs/roadmap/leanisa-blueprint.md:170`) say Clean's generator "would put a row for every pushed
  state in all six tables"; at the pin it fails with `.ambiguousDemand` on the first state,
  since several guardless tables accept it (`findAnswer`), unless `validateGeneration` rejects
  the ensemble first. The conclusion (no theorem uses it) stands.
- **Fix.** Correct both sentences.

### 6. The grind at BLAKE2s, and the factor `N + 1`
- **What.** The completeness bound is in the random-oracle model; at BLAKE2s, whether a grind
  finds a nonce is a fact about one deterministic run and stays unbounded (`prove_eq_none`).
  The bound multiplies `(1 − 2^-17)^fuel` by `N + 1` (all queries) where `L ≤ 6` grinds would
  do; immaterial at fuel 2^24 (2^-155.6 vs ~2^-182).
- **Fix.** None needed for the headline; the sharper `L` needs a state-aware count (report 11).

### 7. The Lean prover is far slower than the generator
- **What.** `proveExecution` on a 1-step ladder trace: 83–143 s; on `field_div` (memory 2^18):
  290 s, 1.9 GB. The generator is 0.2–0.7 s on the same inputs.
- **Fix.** Prover performance work (the blueprint's target is within 1–2 orders of Rust).

### 8. Full-table differential test against Rust
- **What.** Generated tables are compared with Rust only by heights and the main-run row
  `(pc, fp)` multiset; Rust's export lacks the access-count columns, MFCNT/BFCNT, operand
  values, JUMP W/B and `q_flock` (report 03 §8). With item 1 open the memory block differs anyway.
- **Fix.** Extend `emit_fixture` to dump `Witness::columns()`; compare column by column once the
  padding matches (item 1).

### 9. `fillStartTable` is the largest generator stage on big bytecode
- **What.** 0.7 s of 1.5–1.9 s on the 2^19-slot guest: 48 scans of the code. The decidable
  check already uses a one-pass scan over closing jumps (`closeSlots`).
- **Fix.** Use the one-pass search in `fillStarts`, with a proof that it returns the same starts
  (or any starts meeting the spec — `fillStarts_spec` is all the proofs use).

### 10. Clean upstream: verified ensemble generation does not cover leanVM-style VMs
- **What.** Clean's ensemble generator is unverified at the pin and on main; open PR #480's
  `generate_complete` is for prime fields with `2·#interactions < char` (fails for `K`, char 2:
  the multiplicity cells are summed in the field); routing needs the index of `pc` or a
  program-specific guard; read counters are global; padding repeats one row per table where
  leanVM runs distinct closed walks.
- **Fix.** Upstream discussion (comment on Clean #480): char-2-safe multiplicities (exponents of
  `g`, as leanVM does) and a preallocated-block demand mode; leanerVM's generator is a worked
  example of the needed shape.

### Raised by the review and fixed on the branch
- **`StackFits` was decided only by running the generator.** Now a condition on the trace's
  sizes (`execSizes`, `sizes_witnessGen`), decided by `stackFitsB`, exact threshold proved
  (`not_stackFits_of_le` at `t.κ ≥ 25`, `StackFits.of_short`).
- **`proveExecution` ran none of the checks it is proved under.** `proveChecked` runs them
  (`checkExecution_eq_true_iff`); `verify_proveChecked` holds with no hypothesis.
