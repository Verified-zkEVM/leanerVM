/-
  LeanVM.Guest.B1.Gkr.LayerTail

  The tail of a layer of `verify_bus_gkr` (`__loop7`): the rounds between its first and last
  records, the twelve children read and absorbed, their check, the two new coordinates squeezed,
  and the next slot's stores.
-/

module

public import LeanVM.Guest.B1.Gkr.Layer

/-!
# A layer's rounds and children (`__loop7`, G:1716-1777)

* `ly_rounds`: `__loop29`, then `gkr_rounds__L2` at an odd layer index, then `gkr_rounds__L1` at
  an odd depth, run the `L = 2j + sh` rounds from the layer's first record;
* `ly_tail`: the twelve words at the last record's cursor are the three trees' children, their
  products check the last claim, and the sponge after them squeezes the two new coordinates;
* `ly_stores`: the next slot's cells, cursor, values, row, position, `half` and `parity`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Child `i`'s read's first statement in `lyPre`. -/
def lyPos (i : ℕ) : ℕ := 68 + 10 * i + i / 4

theorem lyEvs_check : ∀ i < 12,
    tbStmtsEqb (lyEvT i) ((lyPre.drop (lyPos i)).take (lyEvT i).length) = true := by
  decide +kernel

/-- The words of the children `4m .. 4m + 3`. -/
def lyCh (σ : Val) (m : ℕ) : List E := (List.range 4).map fun i ↦ σ (.n (lyEv (4 * m + i)))

theorem lyCh_length (σ : Val) (m : ℕ) : (lyCh σ m).length = 4 := by simp [lyCh]

theorem lyCh_eq (σ : Val) (m : ℕ) : lyCh σ m = [σ (.n (lyEv (4 * m))), σ (.n (lyEv (4 * m + 1))),
    σ (.n (lyEv (4 * m + 2))), σ (.n (lyEv (4 * m + 3)))] := by
  simp [lyCh, List.range_succ]

/-- Absorbing four scalars at a full queue: one permutation, then the four waiting. -/
theorem tbx_absorbAll_full (s : TbxFs) (hs : s.pend.length = 4) (xs : List E) (hx : xs.length = 4)
    (t : ℕ) : s.absorbAll xs t = ⟨tbxCapOf s.perm, xs.map (·, t)⟩ := by
  match xs, hx with
  | x :: rest, hx =>
    simp only [TbxFs.absorbAll, List.foldl_cons]
    have h1 : s.absorb x t = ⟨tbxCapOf s.perm, [(x, t)]⟩ := by
      simp [TbxFs.absorb, hs, rateScalars]
    rw [h1]
    have := tbx_absorbAll_short ⟨tbxCapOf s.perm, [(x, t)]⟩ rest t (by simp at hx ⊢; omega)
    simp only [TbxFs.absorbAll] at this
    rw [this]
    simp

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- A permutation's thirteen outputs from `b`, and its capacity cells. -/
theorem ly_keccak {ins : List V} {b : ℕ} (hk : (Atom.keccak ins (lyOuts b) false false).Holds rd σ) :
    TbxAllCanonical (ins.map σ) ∧
      (∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (tbxPermOf (ins.map σ)) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = tbxCapOf (tbxPermOf (ins.map σ)) := by
  obtain ⟨-, -, hcan, hout⟩ := tbx_keccakA_perm hk
  have hP : ∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (tbxPermOf (ins.map σ)) false ⟨k, hk⟩ := by
    intro k hk
    have := tbx_outs_eq hout ⟨k, hk⟩ (by simpa [lyOuts] using hk)
    simpa [lyOuts] using this
  refine ⟨hcan, hP, ?_⟩
  simp only [lyCap, tbxCapOf, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rw [hP (8 + 0) (by omega), hP (8 + 1) (by omega), hP (8 + 2) (by omega), hP (8 + 3) (by omega),
    hP (8 + 4) (by omega)]
  rfl

/-- Child `i`'s read: its word at the cursor, packed, and copied. -/
theorem ly_ev {i : ℕ} (h : Stmt.HoldsList C rd σ (lyEvT i) True kret) :
    LoadHolds rd (σ (.n 79)) i (σ (.n (lyEv i))) ∧
      TbxFsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve ∧ σ (.n (lyEv i + 10)) = σ (.n (lyEv i)) := by
  unfold lyEvT at h
  rw [tb_holdsList_append_noRet (by simp [tbxFsNextT, tbxFsPackT]; rfl), tbx_holds_fsNextT] at h
  obtain ⟨⟨⟨hl, hp⟩, -⟩, hc⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hc
  exact ⟨hl, hp, hc⟩

/-- **Four children's permutation**: their cells over the carried capacity. -/
theorem ly_perm_block {m b : ℕ} {cap : List V}
    (hp : ∀ i < 4, TbxFsPackOk σ (.n (lyEv (4 * m + i))) (lyEv (4 * m + i) + 1) dsObserve)
    (hk : (Atom.keccak (lyRate m ++ cap) (lyOuts b) false false).Holds rd σ) :
    (∀ k (hk : k < 13), σ (.n (b + k)) =
      cellsOfState (TbxFs.perm ⟨cap.map σ, (lyCh σ m).map (·, dsObserve)⟩) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = tbxCapOf (TbxFs.perm ⟨cap.map σ, (lyCh σ m).map (·, dsObserve)⟩) := by
  obtain ⟨hcan, hP, hcap⟩ := ly_keccak hk
  have hcell : ∀ i < 4, σ (.n (lyEv (4 * m + i) + 7)) =
      (Keccak.scalarCells (σ (.n (lyEv (4 * m + i)))) dsObserve).1 ∧
      σ (.n (lyEv (4 * m + i) + 9)) = (Keccak.scalarCells (σ (.n (lyEv (4 * m + i)))) dsObserve).2 := by
    intro i hi
    have hc : IsCanonical128 (σ (.n (lyEv (4 * m + i) + 7))) := by
      apply hcan
      simp only [List.map_append, List.mem_append, lyRate, List.map_flatMap, List.mem_flatMap,
        List.mem_range, List.map_cons, List.map_nil, List.mem_cons]
      exact Or.inl ⟨i, hi, Or.inl rfl⟩
    have := tbx_fsPackT_cells (hp i hi)
      (by rw [show lyEv (4 * m + i) + 1 + 6 = lyEv (4 * m + i) + 7 by omega]; exact hc)
    rw [show lyEv (4 * m + i) + 1 + 6 = lyEv (4 * m + i) + 7 by omega,
      show lyEv (4 * m + i) + 1 + 8 = lyEv (4 * m + i) + 9 by omega] at this
    exact Prod.ext_iff.mp this
  have hrate : (lyRate m).map σ = tbxPendCells ((lyCh σ m).map (·, dsObserve)) := by
    simp only [lyRate, lyCh, tbxPendCells, List.map_flatMap, List.flatMap_map, List.map_cons,
      List.map_nil]
    rw [List.flatMap_def, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [(hcell i hi).1, (hcell i hi).2]
  have hins : (lyRate m ++ cap).map σ =
      tbxRateOf ((lyCh σ m).map (·, dsObserve)) ++ cap.map σ := by
    rw [List.map_append, hrate, tbx_rateOf_eq_cells _ (by simp [lyCh_length])]
    simp [lyCh_length]
  rw [hins] at hP hcap
  exact ⟨hP, hcap⟩

/-- A side's new value: its four children's multilinear value at the two new coordinates. -/
theorem ly_val {t b off : ℕ} (h : Stmt.HoldsList C rd σ (lyVal t b off) True kret) :
    σ (.n (b + 8)) = multilinearEval [σ (.n (lyEv (4 * t + 0) + 10)), σ (.n (lyEv (4 * t + 1) + 10)),
      σ (.n (lyEv (4 * t + 2) + 10)), σ (.n (lyEv (4 * t + 3) + 10))]
      [σ (.n 274), σ (.n 294)] ∧ LoadHolds rd (σ (.n 15)) off (σ (.n (b + 8))) := by
  simp only [lyVal, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, l⟩ := h
  refine ⟨?_, l⟩
  rw [e8, e7, e6, e5, e4, e3, e2, e1, e0]
  simp only [multilinearEval, List.foldl, foldPairs, List.headD]
  ring

end Sem

end
end LeanVM.Guest.B1.Tables
