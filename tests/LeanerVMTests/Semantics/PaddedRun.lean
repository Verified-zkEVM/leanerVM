import LeanerVM.Semantics.PaddedRun
import LeanerVMTests.Semantics.PaddedTrace

/-!
# Layer 10 tests: padding keeps the run

The executor's `mul_192bit_word`, padded by one doubling of zeros, is still a valid execution with
the same register sequence, and a read of one of its operands gives the same word on the extended
image. The mutation that makes `image_ext` necessary: with the first operand's cell zeroed, the run
is not valid, because the first `SET_CONSTANT` compares that cell with its immediate.
-/

namespace LeanerVMTests.Semantics.PaddedRun

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Execution LeanerVMTests.Semantics.PaddedTrace

/-! ## A padding keeps the run -/

theorem mul_valid : ValidExecution mulProg mulInput mulTrace := ⟨mulImage_boundary 3, mul_run⟩

/-- The padded trace is a valid execution. -/
theorem mulPadded_valid : ValidExecution mulProg mulInput mulPadded :=
  mulPadded_from.valid (by decide) mul_valid

/-- And its register sequence is the original's. -/
theorem mulPadded_regs : mulPadded.regs = mulTrace.regs :=
  mulPadded_from.regs_eq (by decide) mul_valid

/-- A word read from the original image is the word read from the extension. -/
example : mulPadded.image.read (gpow 2) = some mulX := by
  have h : mulImage.read (gpow 2) = some mulX := by rw [read_lit mulImage 2]; rfl
  exact MemImage.read_mono (κ := minLogMem) (κ' := minLogMem + 1) (L := mulImage)
    (Nat.le_succ _) (by decide) mulPadded_from.image_ext h

/-- The cap is a hypothesis of `PaddedFrom.valid`: padding says only that the memory grows, and a
trace padded past `maxLogMem` is never a valid execution, whatever its run. -/
example (t' : Trace mulProg) (h : maxLogMem < t'.κ) : ¬ ValidExecution mulProg mulInput t' :=
  fun hv ↦ absurd hv.1.2.1 (not_le.mpr h)

/-! ## A change below `2^κ` breaks the run -/

/-- The executor's image with the first operand's cell, `g^2`, zeroed. -/
def alteredImage : MemImage minLogMem := fun i ↦ if (i : ℕ) = 2 then 0 else mulImage i

/-- The first `SET_CONSTANT` fails: cell `2` holds `0`, not `mulX`. -/
theorem altered_step0 : step mulProg alteredImage ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one mulProg)]
  show execute alteredImage ⟨1, 1⟩ (.setConstant (gpow 2) mulX) = _
  simp only [execute, executeWith, one_mul, read_lit alteredImage 2]
  decide +kernel

/-- So the run is not valid: an image that changes a word the run reads is no padding. -/
theorem altered_not_valid :
    ¬ ValidExecution mulProg mulInput (⟨minLogMem, alteredImage, 3⟩ : Trace mulProg) := by
  rintro ⟨-, hrun⟩
  change run mulProg alteredImage 3 ⟨1, 1⟩ = some _ at hrun
  have hne : (⟨1, 1⟩ : Regs K).pc ≠ mulProg.finalPc := by decide +kernel
  rw [run_succ_of_ne hne, altered_step0] at hrun
  exact absurd hrun (by simp)

end LeanerVMTests.Semantics.PaddedRun
