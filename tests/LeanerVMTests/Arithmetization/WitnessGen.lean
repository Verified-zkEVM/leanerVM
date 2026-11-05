import LeanerVM.Arithmetization.WitnessGen
import LeanerVMTests.Arithmetization.Completeness.Theorem

/-!
# Layer 10 tests: the witness generator

`witnessGen_correct` is inhabited at the trace of `PaddedImageRefutation` (one `JUMP` to the
sentinel of the ladder program), and the generator's choices are evaluated there: the fill
starts it searches are fill blocks of the ladder, the run it steps is the one `JUMP`, the `JUMP`
exponent is the least feasible one, and the skeletons it writes number the padded tables' heights.
The full witness has a memory block of `2^17` rows, which the interpreter that evaluates `#guard`
computes too slowly for the test suite; it is evaluated natively by `leanervm-bench 1 witgen`.
-/

namespace LeanerVMTests.Arithmetization.WitnessGen

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Semantics.PaddedImageRefutation
open LeanerVMTests.Semantics.FillBlocks
open LeanerVMTests.Arithmetization.Completeness.Theorem

/-- **The generator's theorem at an instance**: it returns a witness, which satisfies the
constraint statement and represents the trace padded at the searched fill starts. -/
example : ∃ w, witnessGen ladderJumpProg badInput badTrace = some w ∧
    SatisfiedBy ladderJumpProg badInput w ∧
    AssignmentRepresents w (padTrace badTrace (fillStarts ladderJumpProg)) :=
  witnessGen_correct ladderJump_wellFormed badTrace_valid badTrace_fits

/-! ## The fill starts -/

/-- The table of searched starts, evaluated once. -/
def starts : Array ℕ := fillStartTable ladderJumpProg

-- The searched starts of the `XOR` blocks: the first slot of the ladder's 128-block, then the
-- suffixes of it that are blocks of the smaller sizes (any block works, the first is found).
#guard (List.range 8).map (fun k ↦ startsOf starts .xor (sizeAt k)) =
  [1, 65, 97, 113, 121, 125, 127, 128]

-- Every searched start is checked to be a fill block.
#guard fillTables.all fun t ↦ (List.range 8).all fun k ↦
  isFillBlockB ladderJumpProg t (sizeAt k) (startsOf starts t (sizeAt k))

-- The program without `XOR` blocks has none to find (acceptance test 15).
#guard findStart ladderNoXor .xor 128 = none

/-! ## The `JUMP` exponent -/

#guard jumpHeight 0 = some 1
#guard jumpHeight 1 = some 0
#guard jumpHeight 3 = some 3
#guard jumpHeight 7 = some 4
#guard jumpHeight (2 ^ 32 + 1) = none

/-! ## The run -/

/-- A table of powers covering the program. -/
def powers : PowTable := powTable (2 ^ 12)

/-- The run's skeletons, stepped forward once. -/
def runS : List Skel :=
  (runSkelsBy (fetchBy ladderJumpProg powers) (executeWith (readBy badTrace.image powers))
    badTrace.steps Regs.initial #[]).toList

-- One step, the `JUMP` at slot `0`, from the initial registers.
#guard runS.map (fun sk ↦ (sk.ins.opcode, sk.pc == 1, sk.fp == 1)) = [(.jump, true, true)]

/-- A table whose index guesses `5` for `g ^ 7`. -/
def wrongIndex : PowTable := ⟨#[], by simp, (∅ : Std.HashMap UInt64 ℕ).insert (wordKey (gpow 7)) 5⟩

-- A wrong guess is checked and falls back to the scan.
#guard addressIndexBy 12 wrongIndex (gpow 7) = some 7

-- The table holds the powers and indexes them.
#guard (List.range 4096).all fun i ↦ powers.pow i == gpow i && powers.guess (gpow i) == some i

-- The `JUMP` table owes its one run row and a closing jump per traversal of the other tables'
-- fill, one each: six rows, so `2^3`.
#guard jumpHeight (jumpOwed (countsOf (skelCountTable runS))) = some 3

/-- The skeletons of the padded execution, as the generator writes them. -/
def padS : List Skel :=
  runS ++ padSkels badTrace.κ (startsOf starts)
    (planCount (countsOf (skelCountTable runS)) 3)

-- Every table's height is its target: the floors of the five tables and `2^3` for `JUMP`.
#guard fillTables.map (fun op ↦ Skel.count op padS) =
  fillTables.map fun op ↦ tableHeight (countsOf (skelCountTable runS)) 3 op

end LeanerVMTests.Arithmetization.WitnessGen
