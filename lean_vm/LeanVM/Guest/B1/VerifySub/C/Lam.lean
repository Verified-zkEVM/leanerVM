/-
  LeanVM.Guest.B1.VerifySub.C.Lam

  `verify_sub`'s batching (G:3281-3299), honestly.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Ctab
public import LeanVM.Guest.B1.VerifySub.Lam

/-!
# The batching, honestly

`vsLamT_complete`: `λ`'s squeeze, `lam_pool` allocated, and for the `140` batched claims their
value read from `claim_pool` (holding `vals`), their power `λ^(i+1)` stored in `lam_pool` (holding
them), the target accumulated; then `λ^141` times the outputs' claim.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier Finset

@[expose] public section

theorem vsLamT_noNe : vsLamT.all noNeB = true := by decide +kernel

theorem vsLam_notS : ∀ i < 140, Atom.load (.n (1325 + 4 * i)) (.n 7) (vsKept i) ∉ vsSL := by
  decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsLamT_good (hl : args.length = 7) :
    ∀ s ∈ vsLamT, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 1372) (blk := vsLamT)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsLamT_noNe s hs)] at h

theorem vsLamStep_mem {i : ℕ} (hi : i < 140) {s : Stmt} (hs : s ∈ vsLamStep i) : s ∈ vsLamT := by
  rw [vsLamT]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hs⟩))

/-- The batched claims, honestly. -/
theorem vsLam_loop (hl : args.length = 7) {vals : ℕ → E}
    (hpool : ∀ i < 140, LoadHolds rd (vsσ rd w args (.n 7)) (vsKept i) (vals i))
    (hlam : ∀ i < 140, LoadHolds rd (vsσ rd w args (.n 1324)) (vsKept i)
      (vsσ rd w args (.n 1323) ^ (i + 1)))
    {C : CallRel} {kret : List E → Prop} :
    ∀ n ≤ 140, ∀ {nx : Prop}, nx →
      vsσ rd w args (.n (vsPw n)) = vsσ rd w args (.n 1323) ^ (n + 1) ∧
      vsσ rd w args (.n (vsTg n)) = vsσ rd w args (.n 1303) +
        ∑ i ∈ range n, vsσ rd w args (.n 1323) ^ (i + 1) * vals i ∧
      Stmt.HoldsList C rd (vsσ rd w args) ((List.range n).flatMap vsLamStep) nx kret := by
  have hG := vsLamT_good (rd := rd) (w := w) hl
  generalize hσ : vsσ rd w args = σ at *
  intro n
  induction n with
  | zero =>
    intro _ nx h
    refine ⟨by simp [vsPw], by simp [vsTg], h⟩
  | succ n ih =>
    intro hn nx hnx
    have hn' : n < 140 := by omega
    have g := fun s (h : s ∈ vsLamStep n) ↦ hG s (vsLamStep_mem hn' h)
    have r := good_read (w := w) (g (vsLd (1325 + 4 * n) 7 (vsKept n)) (by simp [vsLamStep]))
      (vsLam_notS n hn') (hpool n hn')
    have m1 : Good rd vsSL w σ (.mul (.n (1326 + 4 * n)) (.n (vsPw n)) (.n (1325 + 4 * n))) :=
      g (vsMul _ _ _) (by simp [vsLamStep])
    have a1 : Good rd vsSL w σ (.add (.n (1327 + 4 * n)) (.n (vsTg n)) (.n (1326 + 4 * n))) :=
      g (vsAdd _ _ _) (by simp [vsLamStep])
    have m2 : Good rd vsSL w σ (.mul (.n (1328 + 4 * n)) (.n (vsPw n)) (.n 1323)) :=
      g (vsMul _ _ _) (by simp [vsLamStep])
    have hpw : vsPw n < 1326 + 4 * n := by unfold vsPw; split <;> omega
    simp only [Good] at m1 a1 m2
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show vsPw n < 1326 + 4 * n from hpw,
      show 1325 + 4 * n < 1326 + 4 * n by omega⟩)] at m1
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show vsPw n < 1328 + 4 * n by omega,
      show 1323 < 1328 + 4 * n by omega⟩)] at m2
    obtain ⟨ep, et, -⟩ := ih (by omega) (nx := True) trivial
    have hstep : Stmt.HoldsList C rd σ (vsLamStep n) nx kret := by
      simp only [vsLamStep, Stmt.HoldsList, Stmt.Holds, vsLd, vsMul, vsAdd]
      refine ⟨?_, r.2, m1, a1, m2, hnx⟩
      show LoadHolds rd _ _ _
      rw [ep]; exact hlam n hn'
    refine ⟨?_, ?_, ?_⟩
    · rw [vsPw_succ, m2, ep]; ring
    · rw [vsTg_succ, a1, et, m1, ep, r.1, Finset.sum_range_succ]; ring
    · rw [List.range_succ, List.flatMap_append, holdsList_append]
      exact (ih (by omega) (nx := Stmt.HoldsList C rd σ ((List.range 1).flatMap
        (fun i ↦ vsLamStep (n + i))) nx kret) (by simpa using hstep)).2.2 |> fun h ↦ by
          simpa using h

end
end LeanVM.Guest.B1.VerifySub
