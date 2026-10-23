/-
  LeanVM.Guest.B1.VerifySub.C.Roots

  `verify_sub`'s root and bus challenges (G:3213-3237), honestly.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Sqz

/-!
# The root and the bus challenges, honestly

`vsRootsT_complete`: the last four announced words absorbed (a `KECCAK` atom on canonical cells),
the root's two words read and packed, `assert_canonical` on them (calls in `C`), `bus_alpha`
allocated. `vsAlphasT_complete`: four squeezes (the first with the root waiting), each challenge
stored in `bus_alpha` (holding them).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

theorem vsRootsT_noNe : vsRootsT.all noNeB = true := by decide +kernel

theorem vsRoots_notS : Atom.load (.n 537) (.n 27) 8 ∉ vsSL ∧ Atom.load (.n 547) (.n 27) 9 ∉ vsSL := by
  decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsRootsT_good (hl : args.length = 7) :
    ∀ s ∈ vsRootsT, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 649) (blk := vsRootsT)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsRootsT_noNe s hs)] at h

/-- **The root, honestly.** -/
theorem vsRootsT_complete (hl : args.length = 7)
    (hin : ∀ i ∈ [89, 91, 99, 101, 109, 111, 119, 121, 77, 78, 79, 80, 81],
      IsCanonical128 (vsσ rd w args (.n i)))
    {x0 x1 : E} (hw8 : LoadHolds rd (vsσ rd w args (.n 27)) 8 x0)
    (hw9 : LoadHolds rd (vsσ rd w args (.n 27)) 9 x1)
    {C : CallRel} (hC0 : C "assert_canonical" [x0] [vsσ rd w args (.n 557)])
    (hC1 : C "assert_canonical" [x1] [vsσ rd w args (.n 558)])
    {next : Prop} {kret : List E → Prop} (hn : next) :
    vsσ rd w args (.n 537) = x0 ∧ vsσ rd w args (.n 547) = x1 ∧
      (∀ i ∈ [544, 546, 554, 556], IsCanonical128 (vsσ rd w args (.n i))) ∧
      Stmt.HoldsList C rd (vsσ rd w args) vsRootsT next kret := by
  have hG := vsRootsT_good (rd := rd) (w := w) hl
  have hk : Good rd vsSL w (vsσ rd w args)
      (.keccak [V.n 89, V.n 91, V.n 99, V.n 101, V.n 109, V.n 111, V.n 119, V.n 121, V.n 77, V.n 78,
        V.n 79, V.n 80, V.n 81] (vsRun 524 13) false false) :=
    hG (keccakA [V.n 89, V.n 91, V.n 99, V.n 101, V.n 109, V.n 111, V.n 119, V.n 121, V.n 77,
      V.n 78, V.n 79, V.n 80, V.n 81] (vsRun 524 13)) (by simp [vsRootsT])
  have hcan : AllCanonical ([V.n 89, V.n 91, V.n 99, V.n 101, V.n 109, V.n 111, V.n 119, V.n 121,
      V.n 77, V.n 78, V.n 79, V.n 80, V.n 81].map (vsσ rd w args)) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hin 89 (by simp)
    · exact hin 91 (by simp)
    · exact hin 99 (by simp)
    · exact hin 101 (by simp)
    · exact hin 109 (by simp)
    · exact hin 111 (by simp)
    · exact hin 119 (by simp)
    · exact hin 121 (by simp)
    · exact hin 77 (by simp)
    · exact hin 78 (by simp)
    · exact hin 79 (by simp)
    · exact hin 80 (by simp)
    · exact hin 81 (by simp)
  have hK := keccakA_complete hk hcan
  have g8 : ∀ s ∈ fsNextT (.n 27) 8 537, GoodS rd vsSL w (vsσ rd w args) s :=
    fun s hs ↦ hG s (by simp only [vsRootsT, List.mem_append]; tauto)
  have g9 : ∀ s ∈ fsNextT (.n 27) 9 547, GoodS rd vsSL w (vsσ rd w args) s :=
    fun s hs ↦ hG s (by simp only [vsRootsT, List.mem_append]; tauto)
  obtain ⟨e8, c8a, c8b, -, -⟩ := fsNext_complete (C := C) (next := True) (kret := kret) g8
    vsRoots_notS.1 hw8
  obtain ⟨e9, c9a, c9b, -, -⟩ := fsNext_complete (C := C) (next := True) (kret := kret) g9
    vsRoots_notS.2 hw9
  refine ⟨e8, e9, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact c8a
    · exact c8b
    · exact c9a
    · exact c9b
  · rw [vsRootsT, holdsList_append, holdsList_append, holdsList_append]
    simp only [Stmt.HoldsList, Stmt.Holds, keccakA]
    refine ⟨hK, ?_⟩
    refine (fsNext_complete g8 vsRoots_notS.1 hw8).2.2.2.2 ?_
    refine (fsNext_complete g9 vsRoots_notS.2 hw9).2.2.2.2 ?_
    simp only [Stmt.Holds, vsCall, vsAlloc, List.map_cons, List.map_nil]
    rw [e8, e9]
    exact ⟨hC0, hC1, trivial, hn⟩

end
end LeanVM.Guest.B1.VerifySub
