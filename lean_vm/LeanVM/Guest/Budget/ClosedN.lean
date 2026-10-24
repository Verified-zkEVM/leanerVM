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
theorem deployedBudget_size_mono {Bv Bv' : ℕ} (h : Bv ≤ Bv') (u : End.Work) :
    (deployedBudget Bv).size u ≤ (deployedBudget Bv').size u := by
  apply End.sizeOf_mono
  · simp only [deployedBudget, mainBudget, End.Linear.eval, B1.Main.mainWords]
    have := Nat.mul_le_mul_right u.children
      (show 51 + B1.Main.l5A1 B2C.fs Count.wSB + Bv + B1.Main.agA1 Count.wSK ≤
        51 + B1.Main.l5A1 B2C.fs Count.wSB + Bv' + B1.Main.agA1 Count.wSK by omega)
    omega
  · intro op
    simp only [deployedBudget, mainBudget, End.Linear.eval, mainInstrs]
    have h1 : (Count.mainCounts op).α5 * (B1.Main.l5A1 B2C.fs Count.wSB + Bv) / 1000 ≤
        (Count.mainCounts op).α5 * (B1.Main.l5A1 B2C.fs Count.wSB + Bv') / 1000 :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
    have := Nat.mul_le_mul_right u.children
      (show ((Count.mainCounts op).α5 * B1.Main.l5A0 B2C.fs / 1000 + 1) +
          ((Count.mainCounts op).α5 * (B1.Main.l5A1 B2C.fs Count.wSB + Bv) / 1000 + 1) +
          (Count.mainCounts op).aggC + (Count.mainCounts op).aggD ≤
        ((Count.mainCounts op).α5 * B1.Main.l5A0 B2C.fs / 1000 + 1) +
          ((Count.mainCounts op).α5 * (B1.Main.l5A1 B2C.fs Count.wSB + Bv') / 1000 + 1) +
          (Count.mainCounts op).aggC + (Count.mainCounts op).aggD by omega)
    omega


/-- **The aggregation guest is complete within the deployed budget**, `verify_sub`'s words per
child `661678`: the budget's words `Count.deployedWords 661678`, its instructions
`Count.deployedInstrs 661678 op`. -/
theorem guest_complete_numeric : GuestCompleteWithin (deployedBudget 661678) :=
  Count.deployedBv_eq ▸ guest_complete

end
end LeanVM.Guest.Budget
