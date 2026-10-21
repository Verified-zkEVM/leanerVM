/-
  LeanVM.Guest.B2C.CountsMeet

  B2C's counts under a semantics of `BLAKE2S` are the arithmetization's: the two `runCountB`
  have one body.
-/

module

public import LeanVM.Guest.B2C.CountB
public import LeanVM.Arithmetization.CompletenessB.Count

/-!
# The two counts under a semantics meet

`B2C.runCountB` (`B2C/CountB.lean`, B2C's counts of the honest run) and `Semantics.runCountB`
(`Arithmetization/CompletenessB/Count.lean`, what `Trace.countB` and `Trace.committedSizeB`
count) are defined by the same recursion: `runCountB_eq`. So B2C's bound on the honest run's
counts is a bound on the execution's `Trace.countB` (`countB_eq`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- **B2C's counts are the arithmetization's.** -/
theorem runCountB_eq (S : BlakeSem) {κ : ℕ} (prog : Program) (L : MemImage κ) (op : Opcode) :
    ∀ (n : ℕ) (r : Regs K), runCountB S prog L op n r = LeanVM.Semantics.runCountB S prog L op n r
  | 0, _ => rfl
  | n + 1, r => by
    unfold runCountB LeanVM.Semantics.runCountB
    rcases prog.fetch r.pc with _ | ins <;> rcases stepB S prog L r with _ | r' <;>
      simp only [runCountB_eq S prog L op n]

/-- An execution's count under `S` is B2C's count of its run. -/
theorem countB_eq (S : BlakeSem) {prog : Program} (t : Trace prog) (op : Opcode) :
    t.countB S op = runCountB S prog t.image op t.steps Regs.initial :=
  (runCountB_eq S prog t.image op t.steps Regs.initial).symm

end
end LeanVM.Guest.B2C
