import LeanerVM.Semantics.FillerRows
import LeanerVMTests.Semantics.Executable

/-!
# Unordered filler-row checks

A closed cycle is checked without a main run. State multiplicities are preserved,
including duplicate rows. Failure, an open path, or a sentinel row invalidates the collection.
Hints, useless or duplicated, leave the check unchanged.
-/

namespace LeanerVMTests.Semantics.FillerRows

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Execution LeanerVMTests.Semantics.Executable

/-- A tiny all-one image whose initial JUMP returns to the same registers. -/
def loopImage : MemImage 1 := fun _ ↦ E.ofLimbs 1 0 0

#guard checkFillerRows loopProgram loopImage [] []
#guard checkFillerRows loopProgram loopImage [] [Regs.initial]
#guard checkFillerRows loopProgram loopImage [] [Regs.initial, Regs.initial]
#guard !checkFillerRows loopProgram loopImage [] [Regs.final loopProgram]
#guard !checkFillerRows (oneStep (.setConstant 1 (E.ofLimbs 1 0 0))) loopImage [] [Regs.initial]
#guard !checkFillerRows (oneStep (.setConstant 1 0)) loopImage [] [Regs.initial]
#guard checkFillerRows loopProgram loopImage [1000] [Regs.initial]

/-- Accepted rows have real successors in the same finite collection. -/
example : ∃ next ∈ [Regs.initial], step loopProgram loopImage Regs.initial = some next := by
  have hv : FillerRowsValid loopProgram loopImage [Regs.initial] :=
    (checkFillerRows_eq_true_iff (by decide) loopProgram loopImage [] [Regs.initial]).mp
      (by decide +kernel)
  exact hv.step_mem (List.mem_cons_self)

/-- The equivalence also covers completely useless hints, including duplicate entries. -/
example : checkFillerRows loopProgram loopImage [1000, 1, 1] [Regs.initial] =
    checkFillerRows loopProgram loopImage [] [Regs.initial] :=
  Bool.eq_iff_iff.mpr ((checkFillerRows_eq_true_iff (by decide) _ _ _ _).trans
    (checkFillerRows_eq_true_iff (by decide) _ _ _ _).symm)

end LeanerVMTests.Semantics.FillerRows
