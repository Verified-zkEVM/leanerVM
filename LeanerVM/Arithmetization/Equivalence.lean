/-
  LeanerVM.Arithmetization.Equivalence

  leanISA and its constraint system: constraint soundness and completeness side by side, and the
  equivalence of the two on public inputs.
-/

module

public import LeanerVM.Arithmetization.Soundness
public import LeanerVM.Arithmetization.Completeness.Theorem

@[expose] public section

/-!
# leanISA and its constraints

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), T1 in both directions, at leanVM
pin `a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `9dd71e82`. Category A: nothing
here is transcribed; the statements compose `constraintSoundness`
(`LeanerVM.Arithmetization.Soundness`) and `constraintCompleteness`
(`LeanerVM.Arithmetization.Completeness.Theorem`).

* `leanIsa_constraints` is the pair, on witnesses and traces: for well-formed bytecode, every
  witness satisfying the constraint statement at any memory log-size represents a valid
  execution, and every valid execution that fits the caps (`Trace.Fits`) has a padding, with the
  same steps, represented by a satisfying witness at the padding's log-size.
* `Satisfiable prog input` says the constraint system accepts the public input: some witness at
  some memory log-size satisfies it. `valid_of_satisfiable` and `satisfiable_of_valid` are the
  two directions on inputs, and `satisfiable_iff_valid` the equivalence: for well-formed bytecode
  and an input on which some valid execution fits whenever one exists, the constraint system
  accepts exactly when the program has a valid execution.

## Wrong readings excluded

* The equivalence is not unconditional. A witness's trace need not fit: a memory block of
  log-size `32` leaves no room for the fill frames (`Trace.Fits.room`), and a run whose rows
  exceed a table's cap after padding has no witness at all (`completeness_needs_fit`, tests).
  So the inputs the constraint system accepts lie between those with a fitting valid execution
  and those with any valid execution, and the equivalence takes the hypothesis that closes the
  gap for the input at hand.
* The witness of completeness represents the padded trace, not the given one: the padding adds
  the fill frames above the image and keeps its words and steps (`Trace.PaddedFrom`).
* Soundness needs only that the sentinel slot is not a `JUMP` (`SentinelSafe`); completeness
  needs the fill blocks (`HasFillBlocks`). Both are fields of `WellFormedBytecode`.
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics
open Air.Flat (EnsembleWitness)

variable {prog : Program} {input : PublicInput}

/-- The constraint system of `prog` accepts the public input `input`: at some memory log-size,
some witness satisfies the constraint statement. -/
def Satisfiable (prog : Program) (input : PublicInput) : Prop :=
  ∃ κ, ∃ w : EnsembleWitness (leanIsaEnsemble prog κ), SatisfiedBy prog input w

/-- **leanISA and its constraints.** For well-formed bytecode: every satisfying witness, at any
memory log-size, represents a valid execution (soundness); every valid execution that fits the
caps has a padding with the same steps that a satisfying witness represents (completeness). -/
theorem leanIsa_constraints (hwf : WellFormedBytecode prog) :
    (∀ κ (w : EnsembleWitness (leanIsaEnsemble prog κ)), SatisfiedBy prog input w →
      ∃ t, AssignmentRepresents w t ∧ ValidExecution prog input t) ∧
    (∀ t : Trace prog, ValidExecution prog input t → t.Fits →
      ∃ t', t'.PaddedFrom t ∧ ValidExecution prog input t' ∧
        ∃ w : EnsembleWitness (leanIsaEnsemble prog t'.κ),
          SatisfiedBy prog input w ∧ AssignmentRepresents w t') :=
  ⟨fun _ _ h ↦ constraintSoundness hwf.sentinelSafe h,
    fun _ h hfit ↦ constraintCompleteness hwf h hfit⟩

/-- Soundness on inputs: an accepted input has a valid execution. -/
theorem valid_of_satisfiable (hsafe : SentinelSafe prog) (h : Satisfiable prog input) :
    ∃ t, ValidExecution prog input t := by
  obtain ⟨_, _, hw⟩ := h
  obtain ⟨t, -, ht⟩ := constraintSoundness hsafe hw
  exact ⟨t, ht⟩

/-- Completeness on inputs: an input with a valid execution that fits the caps is accepted. -/
theorem satisfiable_of_valid (hwf : WellFormedBytecode prog) {t : Trace prog}
    (h : ValidExecution prog input t) (hfit : t.Fits) : Satisfiable prog input := by
  obtain ⟨t', -, -, w, hw, -⟩ := constraintCompleteness hwf h hfit
  exact ⟨t'.κ, w, hw⟩

/-- **The equivalence on inputs.** For well-formed bytecode and an input on which some valid
execution fits the caps whenever one exists, the constraint system accepts the input exactly
when the program has a valid execution on it. -/
theorem satisfiable_iff_valid (hwf : WellFormedBytecode prog)
    (hfit : (∃ t, ValidExecution prog input t) → ∃ t, ValidExecution prog input t ∧ t.Fits) :
    Satisfiable prog input ↔ ∃ t, ValidExecution prog input t := by
  refine ⟨valid_of_satisfiable hwf.sentinelSafe, fun h ↦ ?_⟩
  obtain ⟨t, ht, htf⟩ := hfit h
  exact satisfiable_of_valid hwf ht htf

end LeanerVM.Arithmetization
