/-
  LeanVM.Guest.Budget.ClosedN

  The guest's completeness within the deployed budget with every number explicit:
  `verify_sub`'s words per child are `661678` (`Count.deployedBv_eq`).
-/

module

public import LeanVM.Guest.Budget.Closed
public import LeanVM.Guest.Count.VsBound

namespace LeanVM.Guest.Budget

open LeanVM.Node
open LeanVM.Guest.End (GuestCompleteWithin)

@[expose] public section

/-- **Completeness within a larger budget.** -/
theorem guestComplete_mono {b b' : NodeStatement → NodeWitness → ℕ} (h : End.GuestComplete b)
    (hle : ∀ s w, b s w ≤ b' s w) : End.GuestComplete b' :=
  fun seed s w hr hl hca hnz hb => h seed s w hr hl hca hnz ((hle s w).trans hb)

/-- The deployed budget grows with `verify_sub`'s words. -/
theorem deployedBudget_size_mono {Bvf Bvf' : ℕ → ℕ → ℕ} (h : ∀ μ r, Bvf μ r ≤ Bvf' μ r)
    (u : End.Work) : (deployedBudget Bvf).size u ≤ (deployedBudget Bvf').size u := by
  apply End.sizeOf_mono
  · simp only [deployedBudget, mainBudget, End.Linear.eval, B1.Main.mainWords]
    have := List.sum_le_sum (l := u.childShapes) (f := fun p => Bvf p.1 p.2)
      (g := fun p => Bvf' p.1 p.2) fun p _ => h p.1 p.2
    omega
  · intro op
    simp only [deployedBudget, mainBudget, End.Linear.eval, mainInstrs]
    have := List.sum_le_sum (l := u.childShapes)
      (f := fun p => (Count.mainCounts op).α5 * Bvf p.1 p.2 / 1000 + 1)
      (g := fun p => (Count.mainCounts op).α5 * Bvf' p.1 p.2 / 1000 + 1)
      fun p _ => Nat.add_le_add_right (Nat.div_le_div_right (Nat.mul_le_mul_left _ (h p.1 p.2))) 1
    omega

/-- **The aggregation guest is complete within the deployed budget**, `verify_sub`'s words per
child `661678`: the budget's words `Count.deployedWords fun _ _ => 661678`, its instructions
`Count.deployedInstrs (fun _ _ => 661678) op`. -/
theorem guest_complete_numeric : GuestCompleteWithin (deployedBudget fun _ _ => 661678) :=
  Count.deployedBv_eq ▸ guest_complete

end
end LeanVM.Guest.Budget
