import LeanerVM.Arithmetization.Completeness.Theorem
import LeanerVMTests.Semantics.PaddedImageRefutation

/-!
# Layer 10 tests: constraint completeness

`constraintCompleteness` is inhabited. The trace of `PaddedImageRefutation` is a valid execution of
well formed bytecode, one `JUMP` to the sentinel on an image where no `XOR` executes at all; it
fits (`Trace.Fits.of_short`), so the theorem gives it a padded trace and a witness that satisfies
the statement and represents the padded trace. The witness has an `XOR` row for every power of two
its table must have, which the image alone could not give (`image_obstruction`): they are fill
rows, on the frames above the image. What the theorem needs is checked at the instance: the run
has one step, and a padded trace has the same.
-/

namespace LeanerVMTests.Arithmetization.Completeness.Theorem

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Semantics.PaddedImageRefutation
open LeanerVMTests.Semantics.FillBlocks

/-- The sentinel counter of a `2^11`-slot program, as a literal term (status finding E8). -/
local notation "d₀" => (gpow 2047 : K)

/-- The trace of the obstruction: one step, `JUMP` to the sentinel. -/
def badTrace : Trace ladderJumpProg := ⟨minLogMem, badImage d₀, 1⟩

/-- It is a valid execution. -/
theorem badTrace_valid : ValidExecution ladderJumpProg badInput badTrace :=
  bad_valid ladderJumpProg rfl ladderJump_fetch_one

/-- It fits: one step, with room above the image. -/
theorem badTrace_fits : badTrace.Fits :=
  Trace.Fits.of_short (rf := Regs.final ladderJumpProg) badTrace_valid.2 (by decide) (by decide)

/-- **Completeness at an instance.** The padded trace and the witness exist. -/
theorem bad_trace_complete :
    ∃ t' : Trace ladderJumpProg, t'.PaddedFrom badTrace ∧
      ValidExecution ladderJumpProg badInput t' ∧
      ∃ w, SatisfiedBy ladderJumpProg badInput w ∧ AssignmentRepresents w t' :=
  constraintCompleteness ladderJump_wellFormed badTrace_valid badTrace_fits

/-- The witness has an `XOR` row: the table's height is a power of two, which is at least `1`. The
image of `badTrace` admits no `XOR` step (`badImage_no_xor`), so these rows are fill rows, and the
witness represents the padded trace, not `badTrace`. -/
theorem bad_trace_witness_has_xor_row :
    ∃ t' : Trace ladderJumpProg, t'.PaddedFrom badTrace ∧
      ∃ w, SatisfiedBy ladderJumpProg badInput w ∧ AssignmentRepresents w t' ∧
        0 < (tableAt w 0).table.length := by
  obtain ⟨t', hp, -, w, hs, hr⟩ := bad_trace_complete
  refine ⟨t', hp, w, hs, hr, ?_⟩
  obtain ⟨τ, -, hτ⟩ := hs.caps.heights (tableAt w 0)
    (mem_tables_iff.mpr ⟨0, rfl⟩)
  rw [hτ]
  exact Nat.two_pow_pos τ

/-- The padded trace has the one step of the run: padding adds no step of the main run. -/
theorem bad_trace_padded_steps :
    ∃ t' : Trace ladderJumpProg, t'.PaddedFrom badTrace ∧ t'.steps = 1 := by
  obtain ⟨t', hp, -⟩ := bad_trace_complete
  exact ⟨t', hp, hp.steps_eq⟩

end LeanerVMTests.Arithmetization.Completeness.Theorem
