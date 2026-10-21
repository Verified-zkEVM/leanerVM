/-
  LeanVM.Guest.B1.Da.ColumnM

  `da_verify_column` under a hash model: its cells' answered hashes, its part of the vector hash
  as checked rows, its tree answered.
-/

module

public import LeanVM.Guest.B1.Da.VerifyColumn
public import LeanVM.Guest.B1.Da.CellM
public import LeanVM.Guest.B1.Da.VectorM
public import LeanVM.Guest.B1.Da.TreeM

/-!
# A column over a hash model

`da_verify_column__L{store}` (`Column.lean`, `VerifyColumn.lean`) runs the vector cell
(`Meaning_da_vector_dispatchB`), checks each row's cell (`da_verify_cell_model`), fills the gap
rows with the zero cell's digest (hash-free, by transfer) and hashes its tree
(`da_levels_model`). Its meaning over a model, `Meaning_da_verify_columnWith`, is the deployed one
with those three meanings over the model (`da_verify_column_model`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- Row `x` of a column over a hash model: `RowStep` with the cell check's meaning over the
model. -/
def RowCellM (M : HashModel) (store : Bool) (rd : Reader) (lv rb xb node pb x : E) : Prop :=
  ∃ d0 d1 s R a, Meaning_da_verify_cellWith M rd [lv] [d0, d1, s] ∧ LoadHolds rd (rb * x) 0 R ∧
    LoadHolds rd (R * xb) 0 a ∧ LoadHolds rd (R * xb) 1 (a + s) ∧
    CellsAt rd (node * (x * x)) [d0, d1] ∧
    (store = true → ∃ P, LoadHolds rd (pb * x) 0 P ∧ CellsAt rd (P * (xb * xb)) [d0, d1])

/-- One frame of a row loop under `S` (`row_step`'s forward direction). -/
theorem row_stepB {S : BlakeSem} (store : Bool) (rd : Reader) (W lv rb xb node pb : E)
    (C : CallRel) (x : E)
    (h : ∃ fn, coreProgram.find? (rowName store) = some fn ∧
      fn.SemB S C rd (x :: [W, lv, rb, xb, node, pb]) []) :
    RowStep store rd lv rb xb node pb C x ∧ IsInK (x * gen + W) ∧
      (x * gen + W ≠ 0 → C (rowName store) (x * gen :: [W, lv, rb, xb, node, pb]) []) := by
  obtain ⟨fn, hfn, h⟩ := h
  rw [find_row, Option.some.injEq] at hfn
  subst hfn
  cases store
  · simp only [Fn.SemB, rowBody, Bool.false_eq_true, ↓reduceIte, Stmt.HoldsListB, Stmt.HoldsB,
      Atom.HoldsB, List.map_cons, List.map_nil, RowStep, cellsAt_two, ← word_gen, rowName,
      false_implies, and_true] at h ⊢
    obtain ⟨σ, hp, hcall, m10, l11, m12, l13, a14, l14, m15, m16, l7, l8, c17, m18, a19, c20, m21,
      hk, hnext⟩ := h
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
    rw [m10] at l11
    rw [m12] at l13 l14
    rw [a14] at l14
    rw [m16, m15] at l7 l8
    rw [a19, m18, c17] at hk hnext
    rw [m21, c20] at hnext
    exact ⟨⟨_, _, _, _, _, hcall, l11, l13, l14, l7, l8⟩, hk, hnext⟩
  · simp only [Fn.SemB, rowBody, ↓reduceIte, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB,
      List.map_cons, List.map_nil, RowStep, cellsAt_two, ← word_gen, rowName,
      forall_const] at h ⊢
    obtain ⟨σ, hp, hcall, m10, l11, m12, l13, a14, l14, m15, m16, l7, l8, m17, l18, m19, m20, l7',
      l8', c21, m22, a23, c24, m25, hk, hnext, -⟩ := h
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
    rw [m10] at l11
    rw [m12] at l13 l14
    rw [a14] at l14
    rw [m16, m15] at l7 l8
    rw [m17] at l18
    rw [m20, m19] at l7' l8'
    rw [a23, m22, c21] at hk hnext
    rw [m25, c24] at hnext
    exact ⟨⟨_, _, _, _, _, hcall, l11, l13, l14, ⟨l7, l8⟩, _, l18, l7', l8'⟩, hk, hnext⟩

/-- **The row loop under a model**, from `1`. -/
theorem row_loop_model {M : HashModel} (store : Bool) (rd : Reader) (W lv rb xb node pb : E)
    (h : coreProgram.RelB M.sem rd (rowName store) [1, W, lv, rb, xb, node, pb] []) :
    LoopTo W fun j => RowCellM M store rd lv rb xb node pb (gen ^ j) := by
  rw [← pow_zero gen] at h
  obtain ⟨m, hm, hW, hfirst, hall⟩ := loopB_fwd (rowStep_mono store rd lv rb xb node pb)
    (row_stepB store rd W lv rb xb node pb) 0 h
  refine ⟨m, hm, hW, hfirst, fun j hj => ?_⟩
  obtain ⟨d0, d1, s, R, a, hcall, h1, h2, h3, h4, h5⟩ := hall j (Nat.zero_le _) hj
  exact ⟨d0, d1, s, R, a, da_verify_cell_model hcall, h1, h2, h3, h4, h5⟩

/-- The gap loops are free of `BLAKE2S` and call only themselves. -/
theorem freeOn_gap : coreProgram.FreeOn ["__loop485", "__loop487"] = true := by
  decide +kernel

/-- **The gap loop under any semantics**, from `1`: its deployed meaning. -/
theorem gap_loop_B {S : BlakeSem} (store : Bool) (rd : Reader) (W node nb : E)
    (h : coreProgram.RelB S rd (gapName store) [1, W, node, nb] []) :
    LoopTo W fun j => GapStep rd node nb (gen ^ j) := by
  refine (gap_loop_meaning store rd W node nb).mp ?_
  rwa [← relB_iff_rel_of_freeOn (S := S) freeOn_gap (by cases store <;> simp [gapName])]

/-- The tree dispatch on `g^k`, `k < 11`, under a model. -/
theorem dl_dispatchM {M : HashModel} {rd : Reader} {glp node c0 c1 : E}
    (h : ∃ (j : ℕ) (h : j < dlNames.length), glp = ofK (gpow j) ∧
      coreProgram.RelB M.sem rd dlNames[j] [node] [c0, c1]) :
    ∃ k < 11, glp = gen ^ k ∧ Meaning_da_levelsWith M k rd [node] [c0, c1] := by
  obtain ⟨j, hj, hg, hr⟩ := h
  rw [dlNames_length] at hj
  rw [← List.getD_eq_getElem _ ""] at hr
  exact ⟨j, hj, by rw [hg, gen_pow_eq_ofK], da_levels_model j (by omega) _ _ hr⟩

/-- **`da_verify_column__L{store}` over a hash model.** -/
def Meaning_da_verify_columnWith (M : HashModel) (store : Bool) (rd : Reader)
    (args rets : List E) : Prop :=
  ∃ xb nb np gap glp pb ct rb hs ctr, args = [xb, nb, np, gap, glp, pb, ct, rb, hs, ctr] ∧
    rets = [] ∧ ∃ h0 h1 o0 o1 lv node c0 c1,
      CellsAt rd (hs * (xb * xb)) [h0, h1] ∧
      Meaning_da_vector_dispatchB M.sem rd [xb, h0, h1, ctr] [o0, o1, lv] ∧
      CellsAt rd (hs * (xb * gen * (xb * gen))) [o0, o1] ∧
      IsInK nb ∧ (nb ≠ 1 → LoopTo nb fun j => RowCellM M store rd lv rb xb node pb (gen ^ j)) ∧
      IsInK gap ∧ (gap ≠ 1 → LoopTo gap fun j => GapStep rd node nb (gen ^ j)) ∧
      (∃ k < 11, glp = gen ^ k ∧ Meaning_da_levelsWith M k rd [node] [c0, c1]) ∧
      CellsAt rd (ct * (xb * xb)) [c0, c1]

/-- **`da_verify_column__L{store}` is sound under a hash model.** -/
theorem da_verify_column_model {M : HashModel} (store : Bool) (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd (colName store) args rets) :
    Meaning_da_verify_columnWith M store rd args rets := by
  rw [relB_of_find (find_col store)] at h
  simp only [Fn.SemB, colBody, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil, true_and, word_one, word_gen] at h
  obtain ⟨σ, hp, m10, m11, l12, l13, hdisp, c17, m18, m19, m20, l14, l15, m21, m22, c24, a25, c26,
    hk25, hrow, c27, a28, c29, hk28, hgap, hdl, m32, m33, l30, l31, hret⟩ := h
  subst hp hret
  rw [a25, c24] at hk25 hrow
  rw [a28, c27] at hk28 hgap
  rw [c26] at hrow
  rw [c29] at hgap
  rw [m11, m10] at l12 l13
  rw [m20, m19, m18, c17] at l14 l15
  rw [m33, m32] at l30 l31
  refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15),
    σ (.n 16), σ (.n 23), σ (.n 30), σ (.n 31), cellsAt_two.mpr ⟨l12, l13⟩,
    da_vector_dispatch_B hdisp, cellsAt_two.mpr ⟨l14, l15⟩, isInK_one_add.mp hk25,
    fun h => row_loop_model store rd _ _ _ _ _ _ (hrow (one_add_ne_zero.mpr h)),
    isInK_one_add.mp hk28,
    fun h => gap_loop_B store rd _ _ _ (hgap (one_add_ne_zero.mpr h)),
    dl_dispatchM hdl, cellsAt_two.mpr ⟨l30, l31⟩⟩

end
end LeanVM.Guest.B1.Digest
