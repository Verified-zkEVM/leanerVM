/-
  LeanVM.Guest.B1.Place.OsVals

  The body's valuation at its allocation hints: the pointers and sizes of its buffers.
-/

module

public import LeanVM.Guest.B1.Place.OsAllocs
public import LeanVM.Guest.B1.Place.OsLayFacts
public import LeanVM.Guest.B1.Whir.CVals

/-!
# The body's buffers in its valuation

A valuation agreeing with the body's values (`bodyF`) on its values holds, at each allocation hint
(`osAllocsOf`), the buffer's pointer and size word (`vSz`): `lvs_alloc_vals` (the levels),
`res_alloc_vals` (the residual chains), `fin_alloc_vals`, `body_alloc_vals`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- A hint's size word: the constant's word, or the value's. -/
def vSz (σ : Val) (x : V × (ℕ ⊕ V)) : E := x.2.elim gw σ

/-! ## The levels -/

theorem lvs_alloc_vals (c : OsCfg) (σ : Val) : ∀ (lvs : List OsLv) (Ds : List LvDat) (lvl : ℕ)
    (st : OsSt) (σ1 : Val), Ds.length = lvs.length →
    (∀ i, st.k ≤ i → i < (osLevels c lvl lvs st).2.k → σ (.n i) = lvsF c lvl lvs Ds st σ1 i) →
    ((lvsAllocs c lvl lvs st).map Prod.fst).map σ = Ds.flatMap (fun D ↦ [D.sqz, D.wp]) ∧
      (lvsAllocs c lvl lvs st).map (vSz σ) = lvs.flatMap (fun _ ↦ [gw ((c.maxSq + 1) * 5), gw c.maxIl])
  | [], [], _, _, _, _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, _, _, h, _ => absurd h (by simp)
  | lv :: rest, D :: Ds, lvl, st, σ1, hl, hσ => by
    have hb := lvF_bufs c lvl lv st σ1 D
    have hk := osLevel_k_le c lvl lv st
    have hA := osLevelA_k_le c lvl lv st
    have h3 := osSqueezes_k c lvl lv (osLevelA c lvl lv st).2.1
    have hge := osLevels_k_ge c (lvl + 1) rest (osLevel c lvl lv st).2
    have e : (osLevels c lvl (lv :: rest) st).2 = (osLevels c (lvl + 1) rest (osLevel c lvl lv st).2).2 := rfl
    have hw : (osLevelA c lvl lv st).2.1.k + 34 ≤ wpVar c lvl lv (osLevelA c lvl lv st).2.1 - 1 := by
      unfold wpVar; omega
    have hv : ∀ i, st.k ≤ i → i < (osLevel c lvl lv st).2.k → σ (.n i) = lvF c lvl lv st σ1 D i :=
      fun i h1 h2 ↦ by
        rw [hσ i h1 (by rw [e]; omega)]
        show seqF σ1 st.k (osLevel c lvl lv st).2.k (lvF c lvl lv st σ1 D) _ i = _
        exact seqF_lt h2
    have ih := lvs_alloc_vals c σ rest Ds (lvl + 1) (osLevel c lvl lv st).2
      (fill σ1 st.k (osLevel c lvl lv st).2.k (lvF c lvl lv st σ1 D)) (by simpa using hl)
      (fun i h1 h2 ↦ by
        rw [hσ i (by have := osLevel_k_ge c lvl lv st; omega) (by rw [e]; exact h2)]
        show seqF σ1 st.k (osLevel c lvl lv st).2.k (lvF c lvl lv st σ1 D) _ i = _
        exact seqF_ge h1)
    have hwv : (osSqueezes c lvl lv (osLevelA c lvl lv st).2.1).2.k + lv.queries + 1 =
        wpVar c lvl lv (osLevelA c lvl lv st).2.1 := rfl
    have hwv' : (osSqueezes c lvl lv (osLevelA c lvl lv st).2.1).2.k + lv.queries =
        wpVar c lvl lv (osLevelA c lvl lv st).2.1 - 1 := by unfold wpVar; omega
    simp only [lvsAllocs, lvAllocs, List.map_append, List.map_cons, List.map_nil, List.flatMap_cons,
      osHeapA, vSz, Sum.elim_inr]
    refine ⟨?_, ?_⟩
    · rw [ih.1, hv _ (by omega) (by omega), hb.2.1, hwv, hv _ (by omega) (by omega), hb.2.2.2]
    · rw [ih.2, hv _ (by omega) (by omega), hb.1, hwv', hv _ (by omega) (by omega), hb.2.2.1]

/-! ## The residual chains -/

theorem res_alloc_vals (c : OsCfg) (σ : Val) (ich bd ls : ℕ) (RC acc P W I L : ℕ → E)
    (D : ℕ → ℕ → E) : ∀ (levels : List OsLv) (lvl k : ℕ) (σ1 : Val),
    (∀ i, k ≤ i → i < (osResiduals c ich bd ls lvl levels k).2 →
      σ (.n i) = residualsF c bd RC acc P W I L D lvl levels k σ1 i) →
    ((resAllocs c ich bd ls lvl levels k).map Prod.fst).map σ =
        (List.range levels.length).map (fun j ↦ RC (lvl + j)) ∧
      (resAllocs c ich bd ls lvl levels k).map (vSz σ) = levels.map (fun _ ↦ gw (c.maxQ + 1))
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | lv :: rest, lvl, k, σ1, hσ => by
    have h1 := osResidual_k c ich bd ls lvl lv k
    have h2 := osResiduals_k c ich bd ls (lvl + 1) rest (osResidual c ich bd ls lvl lv k).2
    have e : (osResiduals c ich bd ls lvl (lv :: rest) k).2 =
        (osResiduals c ich bd ls (lvl + 1) rest (osResidual c ich bd ls lvl lv k).2).2 := rfl
    have ek := osResidual_k_eq c ich bd ls lvl lv k
    have hv : ∀ i, k ≤ i → i < k + 9 →
        σ (.n i) = residualF c lvl lv bd k σ1 (RC lvl) (acc lvl) (P lvl) (W lvl) (I lvl) (L lvl)
          (D lvl) i := fun i g1 g2 ↦ by
      rw [hσ i g1 (by rw [e]; omega)]
      show seqF σ1 k (osResidual c 0 bd 0 lvl lv k).2 _ _ i = _
      exact seqF_lt (by rw [← ek]; omega)
    have hv2 : ∀ i, k ≤ i → i < k + 9 → residualF c lvl lv bd k σ1 (RC lvl) (acc lvl) (P lvl) (W lvl)
        (I lvl) (L lvl) (D lvl) i = (resPreVals c (lv.queries / 2) (RC lvl) (acc lvl)).getD (i - k) 0 :=
      fun i _ g2 ↦ seqF_lt g2
    have ih := res_alloc_vals c σ ich bd ls RC acc P W I L D rest (lvl + 1)
      (osResidual c ich bd ls lvl lv k).2
      (fill σ1 k (osResidual c 0 bd 0 lvl lv k).2
        (residualF c lvl lv bd k σ1 (RC lvl) (acc lvl) (P lvl) (W lvl) (I lvl) (L lvl) (D lvl)))
      (fun i g1 g2 ↦ by
        rw [hσ i (by omega) (by rw [e]; exact g2)]
        show seqF σ1 k (osResidual c 0 bd 0 lvl lv k).2 _ _ i = _
        rw [seqF_ge (by rw [← ek]; exact g1), ek])
    have ih1 := ih.1
    rw [List.map_map] at ih1
    simp only [resAllocs, List.map_cons, osHeapA, vSz, Sum.elim_inr, List.length_cons,
      List.range_succ_eq_map, List.map_map]
    refine ⟨?_, ?_⟩
    · rw [ih1, hv _ (by omega) (by omega), hv2 _ (by omega) (by omega)]
      simp only [resPreVals, Nat.add_sub_cancel_left, List.getD_cons_succ, List.getD_cons_zero,
        Nat.add_zero, List.cons.injEq, true_and]
      exact List.map_congr_left fun j _ ↦ by simp only [Function.comp_apply]; congr 1; omega
    · rw [ih.2, hv _ le_rfl (by omega), hv2 _ le_rfl (by omega)]
      simp [resPreVals]

end
end LeanVM.Guest.B1
