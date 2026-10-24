/-
  LeanVM.Guest.Lift.OqFitsAll

  Every deployed specialization of `opening_queries` fits its frames (`OqFits`), and so does
  every `open_stacked` candidate (`OsFitsAt`).
-/

module

public import LeanVM.Guest.Lift.OqFitsS0
public import LeanVM.Guest.Lift.OqFitsS1
public import LeanVM.Guest.Lift.OqFitsS2
public import LeanVM.Guest.Lift.OqFitsS3
public import LeanVM.Guest.B1.Place.OsCandAll

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **Every deployed `opening_queries`' frames fit its runs**, for certificates whose runs fit
their frames and meet only at common values. -/
theorem opening_queries_fits (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    ∀ p ∈ openingQueriesLoops, OqFits fs cert p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  intro p hp
  simp only [openingQueriesLoops, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqF_413 fs cert hfit hap
  · exact oqF_449 fs cert hfit hap
  · exact oqF_701 fs cert hfit hap
  · exact oqF_575 fs cert hfit hap
  · exact oqF_598 fs cert hfit hap
  · exact oqF_623 fs cert hfit hap
  · exact oqF_654 fs cert hfit hap
  · exact oqF_425 fs cert hfit hap
  · exact oqF_418 fs cert hfit hap
  · exact oqF_524 fs cert hfit hap
  · exact oqF_491 fs cert hfit hap
  · exact oqF_489 fs cert hfit hap
  · exact oqF_761 fs cert hfit hap
  · exact oqF_600 fs cert hfit hap
  · exact oqF_533 fs cert hfit hap
  · exact oqF_692 fs cert hfit hap
  · exact oqF_563 fs cert hfit hap
  · exact oqF_721 fs cert hfit hap
  · exact oqF_743 fs cert hfit hap
  · exact oqF_632 fs cert hfit hap
  · exact oqF_515 fs cert hfit hap
  · exact oqF_422 fs cert hfit hap
  · exact oqF_568 fs cert hfit hap
  · exact oqF_474 fs cert hfit hap
  · exact oqF_471 fs cert hfit hap
  · exact oqF_683 fs cert hfit hap
  · exact oqF_602 fs cert hfit hap
  · exact oqF_745 fs cert hfit hap
  · exact oqF_433 fs cert hfit hap
  · exact oqF_551 fs cert hfit hap
  · exact oqF_487 fs cert hfit hap
  · exact oqF_586 fs cert hfit hap
  · exact oqF_755 fs cert hfit hap
  · exact oqF_643 fs cert hfit hap
  · exact oqF_665 fs cert hfit hap
  · exact oqF_556 fs cert hfit hap
  · exact oqF_455 fs cert hfit hap
  · exact oqF_452 fs cert hfit hap
  · exact oqF_605 fs cert hfit hap
  · exact oqF_519 fs cert hfit hap
  · exact oqF_517 fs cert hfit hap
  · exact oqF_678 fs cert hfit hap
  · exact oqF_542 fs cert hfit hap
  · exact oqF_468 fs cert hfit hap
  · exact oqF_710 fs cert hfit hap
  · exact oqF_732 fs cert hfit hap
  · exact oqF_614 fs cert hfit hap
  · exact oqF_501 fs cert hfit hap
  · exact oqF_676 fs cert hfit hap
  · exact oqF_439 fs cert hfit hap
  · exact oqF_436 fs cert hfit hap
  · exact oqF_591 fs cert hfit hap
  · exact oqF_505 fs cert hfit hap
  · exact oqF_503 fs cert hfit hap
  · exact oqF_680 fs cert hfit hap
  · exact oqF_757 fs cert hfit hap

open LeanVM.Guest.B1.Whir in
/-- **A configuration's `opening_queries` fit their frames** when its levels name deployed
specializations (`NamesOk`). -/
theorem osFitsAt_of_names (fs : String → ℕ) (cert : String → V → ℕ) (hfit : Lift.RunsFit fs cert)
    (hap : Lift.RunsApart cert) {c : OsCfg} (hn : ∀ l < c.levels.length, NamesOk c l (lvAt c l)) :
    OsFitsAt fs cert c := by
  intro l hl
  have hloop : (osQueriesName l (lvAt c l), oqLoopOf (osQueriesName l (lvAt c l)), osQShape c l,
      (lvAt c l).queries % 2 * (if l = 0 then 1 else 0)) ∈ openingQueriesLoops :=
    shapes_loops (hn l hl).2.2.2.2.2.1
  have h := opening_queries_fits fs cert hfit hap _ hloop
  dsimp only at h
  exact h

open LeanVM.Guest.B1.Whir in
/-- **Every `open_stacked` candidate's `opening_queries` fit their frames**, for certificates
whose runs fit their frames and meet only at common values. -/
theorem osFitsAt_all (fs : String → ℕ) (cert : String → V → ℕ) (hfit : Lift.RunsFit fs cert)
    (hap : Lift.RunsApart cert) (μ r : ℕ) (h1 : 22 ≤ μ) (h2 : μ ≤ 28) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    OsFitsAt fs cert (osCfg (candidate μ r)) := by
  obtain ⟨cfg, -, hnames, -⟩ := candB_sound (candB_all μ r h1 h2 h3 h4)
  exact osFitsAt_of_names fs cert hfit hap fun l hl ↦ hnames l hl

end
end LeanVM.Guest.B1
