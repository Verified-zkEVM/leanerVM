import LeanerVM.Semantics.Cycle
import LeanerVMTests.Semantics.Checker

/-!
# Filler-cycle contract tests

A concrete closed JUMP cycle is accepted without supplying a main run. Mutations reject an
empty filler, an open path, an incorrect intermediate register pair, a read mismatch, and a
transition beginning at the sentinel. No successful main run alone certifies these fillers.
-/

namespace LeanerVMTests.Semantics.Cycle

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Execution LeanerVMTests.Semantics.Checker

/-- A tiny all-one image whose initial JUMP returns to the same registers. -/
def loopImage : MemImage 1 := fun _ ↦ E.ofLimbs 1 0 0

/-- A one-row closed filler, including its repeated endpoint. -/
def loopCycle : Cycle := ⟨1, ![Regs.initial, Regs.initial]⟩

/-- The cycle contract has a kernel-checked concrete inhabitant. -/
theorem loop_valid : loopCycle.Valid loopProgram loopImage :=
  (checkCycle_eq_true_iff (by decide) _ _ _).mp (by decide +kernel)

example : run loopProgram loopImage 1 Regs.initial = some Regs.initial := loop_valid.run

#guard checkCycle loopProgram loopImage loopCycle
#guard !checkCycle loopProgram loopImage ⟨0, ![Regs.initial]⟩
#guard !checkCycle loopProgram loopImage ⟨1, ![Regs.initial, ⟨g, 1⟩]⟩
#guard !checkCycle loopProgram loopImage ⟨2, ![Regs.initial, ⟨g, 1⟩, Regs.initial]⟩
#guard !checkCycle loopProgram loopImage ⟨1, ![Regs.final loopProgram, Regs.final loopProgram]⟩
#guard !checkCycle (κ := 1) loopProgram (fun _ ↦ (0 : E)) loopCycle
#guard !checkCycle (oneStep (.setConstant 1 (E.ofLimbs 1 0 0))) loopImage
  ⟨1, ![Regs.initial, ⟨g, 1⟩]⟩

end LeanerVMTests.Semantics.Cycle
