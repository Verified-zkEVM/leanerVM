import LeanerVM.Semantics.FillerRows
import LeanerVMTests.Semantics.Checker

/-!
# Unordered filler-row checks

A closed cycle is checked without a main run. State multiplicities are preserved,
including duplicate rows. Failure, an open path, or a sentinel row invalidates the collection.
-/

namespace LeanerVMTests.Semantics.FillerRows

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Execution LeanerVMTests.Semantics.Checker

/-- A tiny all-one image whose initial JUMP returns to the same registers. -/
def loopImage : MemImage 1 := fun _ ↦ E.ofLimbs 1 0 0

#guard checkFillerRows loopProgram loopImage []
#guard checkFillerRows loopProgram loopImage [Regs.initial]
#guard checkFillerRows loopProgram loopImage [Regs.initial, Regs.initial]
#guard !checkFillerRows loopProgram loopImage [Regs.final loopProgram]
#guard !checkFillerRows (oneStep (.setConstant 1 (E.ofLimbs 1 0 0))) loopImage [Regs.initial]
#guard !checkFillerRows (oneStep (.setConstant 1 0)) loopImage [Regs.initial]

/-- Accepted rows have real successors in the same finite collection. -/
example : ∃ next ∈ [Regs.initial], step loopProgram loopImage Regs.initial = some next := by
  have hv : FillerRowsValid loopProgram loopImage [Regs.initial] :=
    (checkFillerRows_eq_true_iff (by decide) _ _ _).mp (by decide +kernel)
  exact hv.step_mem (List.mem_cons_self)

end LeanerVMTests.Semantics.FillerRows
