import LeanerVM.Arithmetization.Equivalence
import LeanerVMTests.Arithmetization.Completeness.Theorem

/-!
# Layer 10 tests: leanISA and its constraints

A classic test. The equivalence of `LeanerVM.Arithmetization.Equivalence` at an instance: the
one-step `JUMP` trace of the completeness tests is valid and fits, so its input is accepted, and
the fit hypothesis of `satisfiable_iff_valid` holds there, so the equivalence is not vacuous.
-/

namespace LeanerVMTests.Arithmetization.Equivalence

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Semantics.PaddedImageRefutation
open LeanerVMTests.Semantics.FillBlocks
open LeanerVMTests.Arithmetization.Completeness.Theorem

/-- The input of the one-step trace is accepted. -/
theorem bad_satisfiable : Satisfiable ladderJumpProg badInput :=
  satisfiable_of_valid ladderJump_wellFormed badTrace_valid badTrace_fits

/-- The equivalence's hypothesis holds on that input, and both sides are true. -/
example : Satisfiable ladderJumpProg badInput ↔ ∃ t, ValidExecution ladderJumpProg badInput t :=
  satisfiable_iff_valid ladderJump_wellFormed fun _ ↦ ⟨badTrace, badTrace_valid, badTrace_fits⟩

/-- Soundness on inputs recovers a valid execution from the accepted input. -/
example : ∃ t, ValidExecution ladderJumpProg badInput t :=
  valid_of_satisfiable ladderJump_wellFormed.sentinelSafe bad_satisfiable

end LeanerVMTests.Arithmetization.Equivalence
