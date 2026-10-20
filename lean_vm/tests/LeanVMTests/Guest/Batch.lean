import LeanVM.Guest.Batch.Children

/-!
# Tests: the batching's soundness

* `rounds_sound`, `batch_sound` and `children_sound` rest on Lean's three standard axioms.
* **The condition doing the work.** `rounds_sound` needs the final claim to be `f` at the
  challenges: with no round, a false first claim (`1`, the cube sum of `0` being `0`) leaves no
  bad round, and it is the final check that fails.
* **The bound is attained.** A round's gap has at most two roots (`quadratic_roots`), and
  `x² + x` has exactly two, `0` and `1`, in characteristic two.
-/

namespace LeanVMTests.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Guest.B1 LeanVM.Guest.Batch

/-- info: 'LeanVM.Guest.Batch.rounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.rounds_sound

/-- info: 'LeanVM.Guest.Batch.batch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_sound

/-- info: 'LeanVM.Guest.Batch.children_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.children_sound

/-- Without rounds, a false first claim leaves no bad round: the final check is what fails. -/
example (cv : Digest) :
    (1 : E) ≠ cubeSum 0 (fun _ ↦ 0) [] ∧ (¬ ∃ j < 0, BadRound 0 (fun _ ↦ 0) [] 1 cv j) ∧
      (bsRun [] 1 cv).1.2 ≠ (fun _ ↦ (0 : E)) (roundChallenges [] 1 cv) := by
  refine ⟨by simp [cubeSum], by simp, ?_⟩
  simp [bsRun]

/-- `x² + x` has exactly two roots, `0` and `1`. -/
example : {x : E | x ^ 2 + x = 0}.ncard = 2 := by
  have : {x : E | x ^ 2 + x = 0} = {0, 1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h' : x * (x + 1) = 0 := by rw [← h]; ring
      rcases mul_eq_zero.mp h' with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by
          have := congrArg (· + 1) h1
          simpa [add_assoc, CharTwo.add_self_eq_zero] using this)
    · rintro (rfl | rfl) <;> simp [CharTwo.add_self_eq_zero]
  rw [this, Set.ncard_pair zero_ne_one]

end LeanVMTests.Guest.Batch
