import LeanerVM.Arithmetization.HypothesisChecks
import LeanerVMTests.Arithmetization.Completeness.Theorem
import LeanerVMTests.Arithmetization.Statement

/-!
# Layer 10 tests: checking the hypotheses of completeness

The checks are evaluated on the fixtures of completeness and of the constraint statement, and
agree there with what is proved: the ladder program with a `JUMP` at slot `0` is well formed and
its one-step trace fits; the program of the statement's fill test runs validly and fits but is not
well formed bytecode (its blocks are not the compiler's). One mutation per load-bearing condition
makes a check fail: a program without `XOR` blocks; the ladder without its `128`-slot `XOR` block,
whose smaller blocks are all still there; the ladder with a `JUMP` at the sentinel slot; a trace
whose memory is at the cap; and run rows over the cap for `rows` and for `jump`.
-/

namespace LeanerVMTests.Arithmetization.HypothesisChecks

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Semantics.FillBlocks
open LeanerVMTests.Semantics.PaddedImageRefutation
open LeanerVMTests.Arithmetization.Completeness.Theorem
open LeanerVMTests.Arithmetization.Statement

/-! ## Well formed bytecode -/

-- The ladder with a `JUMP` at slot `0` is well formed, as `ladderJump_wellFormed` proves.
#guard wellFormedB ladderJumpProg
#guard decide (WellFormedBytecode ladderJumpProg)

/-- The check agrees with the proof. -/
example : wellFormedB ladderJumpProg = true :=
  (wellFormedB_eq_true_iff _).mpr ladderJump_wellFormed

-- The closing jumps of the ladder: eight per table, below the sentinel.
#guard (closeSlots ladderJumpProg).length = 48

-- No `XOR` block at all (acceptance test 15).
#guard !wellFormedB ladderNoXor

/-- The check agrees with the proof. -/
example : wellFormedB ladderNoXor = false :=
  Bool.eq_false_iff.mpr fun h ↦ ladderNoXor_no_blocks ((wellFormedB_eq_true_iff _).mp h).2

/-- The ladder with slot `2`, inside the `128`-slot `XOR` block, replaced by a `SET_CONSTANT`. -/
def noXor128Prog : Program :=
  ⟨11, by decide, fun i ↦ if (i : ℕ) = 2 then .setConstant (gpow 0) 0 else ladderJumpProg.code i⟩

-- Every smaller `XOR` block is still there, but the largest is not, so the bytecode is not well
-- formed.
#guard [64, 32, 16, 8, 4, 2, 1].all fun s ↦ (findStart noXor128Prog .xor s).isSome
#guard (findStart noXor128Prog .xor 128).isNone
#guard !wellFormedB noXor128Prog

/-- The ladder with a `JUMP` at the sentinel slot. -/
def jumpSentinelProg : Program :=
  ⟨11, by decide, fun i ↦
    if (i : ℕ) = 2047 then .jump (gpow 0) (gpow 0) (gpow 0) else ladderJumpProg.code i⟩

-- The fill blocks are there, the sentinel is not safe.
#guard hasFillBlocksB jumpSentinelProg
#guard !wellFormedB jumpSentinelProg

-- The statement's fill program runs validly but is not well formed bytecode: its blocks are not
-- the compiler's dummies.
#guard decide (SentinelSafe fillProg)
#guard !wellFormedB fillProg

/-! ## Traces that fit -/

/-- The guess table of the fixtures' addresses. -/
def powers : Std.HashMap UInt64 ℕ := powTable (2 ^ 12)

-- The one-step trace of the ladder fits, as `badTrace_fits` proves.
#guard fitsBy ladderJumpProg badTrace (guessOf powers)

/-- The check agrees with the proof. -/
example : fitsBy ladderJumpProg badTrace (guessOf powers) = true :=
  (fitsBy_eq_true_iff badTrace_valid _).mpr badTrace_fits

-- The forward pass counts the one `JUMP` row.
#guard (runCountTableBy ladderJumpProg badTrace (guessOf powers)).toList = [0, 0, 0, 0, 1, 0]

-- The statement's four-step trace fits.
#guard fitsBy fillProg fillTrace (guessOf powers)

/-- The ladder's trace with its memory at the cap. -/
def capTrace : Trace ladderJumpProg := ⟨maxLogMem, fun _ ↦ 0, 1⟩

-- No room above the image.
#guard !fitsBy ladderJumpProg capTrace (guessOf powers)

/-- A trace whose memory is at the cap does not fit, decided without its rows. -/
example : ¬ capTrace.Fits := by
  rw [← fitsRowsB_eq_true_iff]
  simp [fitsRowsB, capTrace]

-- Rows over the cap fail `rows`; `JUMP` rows at the cap fail `jump`, which owes five more closing
-- jumps; with a `JUMP` table that leaves the room it fits.
#guard !fitsRowsB 16 fun _ ↦ 2 ^ 32 + 1
#guard !fitsRowsB 16 fun op ↦ if op = .jump then 2 ^ 32 else 0
#guard fitsRowsB 16 fun op ↦ if op = .jump then 2 ^ 32 - 5 else 0

-- `JumpFeasible` is decided.
#guard decide (JumpFeasible 6) && !decide (JumpFeasible (2 ^ 32 + 1))

end LeanerVMTests.Arithmetization.HypothesisChecks
