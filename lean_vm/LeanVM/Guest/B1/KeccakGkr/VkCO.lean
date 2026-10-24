/-
  LeanVM.Guest.B1.KeccakGkr.VkCO

  `verify_keccak`'s openings on its layout.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCN

/-!
# The openings, on the layout

`rets_good`: a call's returns are the oracle's. `step_rets`: layer `s`'s returns are its honest
ones. `out_on`: the committed outputs' opening holds on the layout, its check by the honest run's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **A call's returns are the oracle's.** -/
theorem rets_good {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {pre : List Stmt} {o : ℕ}
    (hg : ∀ s ∈ pre, pinB s = false → GoodS rd S w σ s) :
    ∀ x ∈ pre.filterMap (callSFO o), ∀ v ∈ x.2.2.2, σ v = w v.idx := by
  intro x hx v hv
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.mp hx
  cases s with
  | call f args rets =>
    simp only [callSFO, Main.Stmt.callS, Option.some.injEq] at hsx
    subst hsx
    exact hg _ hs rfl v hv
  | dispatch x fs args rets =>
    simp only [callSFO, Option.some.injEq] at hsx
    subst hsx
    exact hg _ hs rfl v hv
  | callIf c f args =>
    simp only [callSFO, Main.Stmt.callS, Option.some.injEq] at hsx
    subst hsx
    simp at hv
  | _ => simp [callSFO, Main.Stmt.callS] at hsx

namespace VkData

variable {D : VkData} {rd : Reader} {B curE chiE olE zvE slE : ℕ} {ls : ℕ → ℕ}

theorem calls_good (h : D.Ok) {σ : Val} (hσd : σ = D.val rd B curE chiE olE zvE slE) :
    ∀ x ∈ vkCalls D.odd, ∀ v ∈ x.2.2.2, σ v = D.w B curE v.idx := by
  have hg : ∀ s ∈ vkPre, pinB s = false → GoodS rd vkSt (D.w B curE) σ s := fun s hs hp ↦ by
    subst hσd; exact (val_good h).2.1 s (by rw [vkT_pre]; exact List.mem_append_left _ hs) hp
  have hk : vkPre.filterMap (callSFO D.odd) = vkCalls D.odd := by
    have : D.odd < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases hD : D.odd
    · exact vkPre_kernel.2.2.2.2.1
    · exact vkPre_kernel.2.2.2.2.2
  rw [← hk]
  exact rets_good hg

/-- **Layer `s`'s returns are its honest ones.** -/
theorem step_rets (h : D.Ok) {σ : Val} (hσd : σ = D.val rd B curE chiE olE zvE slE) {s : ℕ}
    (hs : s < 12) {j : ℕ} (hj : j < 6) :
    σ (.n (stepE s - 6 + j)) = ((D.layer s).rets (firstOf s) (ptr (curE + D.lcur s))).getD j 0 := by
  have hm : stepCall D.odd s ∈ vkCalls D.odd :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩))
  have hE := stepE_eq s hs
  have hv : V.n (stepE s - 6 + j) ∈ (stepCall D.odd s).2.2.2 := by
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · simp only [stepCall, ↓reduceIte, List.mem_map, List.mem_range]
      exact ⟨j, hj, by simp only [stepTailSz, ↓reduceIte] at hE; congr 1⟩
    · simp only [stepCall, show s ≠ 0 by omega, ↓reduceIte, List.mem_map, List.mem_range]
      exact ⟨j, hj, by simp only [stepTailSz, show s ≠ 0 by omega, ↓reduceIte] at hE; congr 1; omega⟩
  rw [calls_good h hσd _ hm _ hv]
  exact w_layer hs hj

theorem beta_cap_length (s : ℕ) : ((D.layer s).beta (firstOf s)).2.cap.length = 5 :=
  (sq_ok _).2.1

theorem rets_cap (h : D.Ok) {s : ℕ} (hs : s < 12) {cur : E} {j : ℕ} (hj : j < 5) :
    ((D.layer s).rets (firstOf s) cur).getD j 0 = (D.chain (s + 1)).2.cap.getD j 0 := by
  rw [D.layer_succ h hs, LayerData.rets,
    List.getD_append _ _ _ _ (by rw [beta_cap_length]; exact hj)]

theorem rets_cur (h : D.Ok) {s : ℕ} (hs : s < 12) :
    ((D.layer s).rets (firstOf s) (ptr (curE + D.lcur s))).getD 5 0 = ptr (curE + D.lcur (s + 1)) := by
  rw [LayerData.rets, List.getD_append_right _ _ _ _ (by rw [beta_cap_length]),
    beta_cap_length, ptr_mul_gen, D.layer_y h hs.le]
  simp only [Nat.sub_self, List.getD_cons_zero, lcur]
  congr 1
  ring

end VkData

end
end LeanVM.Guest.B1.VerifySub
