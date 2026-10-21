/-
  LeanVM.Guest.B1.Comp.Da.Column

  The column loops and `da_verify_column` over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Da.Tree
public import LeanVM.Guest.B1.Comp.Da.Cell
public import LeanVM.Guest.B1.Comp.Da.Vector

/-!
# A column over a completeness model

The backward half of `da_verify_column_iff` over a `CompModel`: the row loop's cells over the
model's answers (`RowCellM CM.hm`, W2's, through `da_verify_cell_comp`), the gap loop free of
`BLAKE2S`, the vector hash's 96 rows under the model's semantics
(`Meaning_da_vector_dispatchB CM.sem`), the column tree answered (`Meaning_da_levelsWith CM.hm`):
`Meaning_da_verify_columnComp CM store` and `da_verify_column_comp`. W2's
`Meaning_da_verify_columnWith M` states the vector's rows under `M.sem`, so the meaning over a
completeness model names `CM.sem` there. At `CompModel.deployed` the deployed backward direction
(`da_verify_column_of_comp`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

/-- One frame of a row loop under any semantics, backward (`row_step`'s backward half). -/
theorem row_step_bwdB {S : BlakeSem} (store : Bool) (rd : Reader) (W lv rb xb node pb x : E)
    (h : RowStep store rd lv rb xb node pb (coreProgram.RelB S rd) x) (hk : IsInK (x * gen + W))
    (hnext : x * gen + W ≠ 0 →
      coreProgram.RelB S rd (rowName store) (x * gen :: [W, lv, rb, xb, node, pb]) []) :
    ∃ fn, coreProgram.find? (rowName store) = some fn ∧
      fn.SemB S (coreProgram.RelB S rd) rd (x :: [W, lv, rb, xb, node, pb]) [] := by
  refine ⟨_, find_row store, ?_⟩
  cases store
  · simp only [Fn.SemB, rowBody, Bool.false_eq_true, ↓reduceIte, Stmt.HoldsListB, Stmt.HoldsB,
      Atom.HoldsB, List.map_cons, List.map_nil, and_true]
    obtain ⟨d0, d1, s, R, a, hcall, l11, l13, l14, h7, -⟩ := h
    obtain ⟨l7, l8⟩ := cellsAt_two.mp h7
    refine ⟨listVal [x, W, lv, rb, xb, node, pb, d0, d1, s, rb * x, R, R * xb, a, a + s, x * x,
      node * (x * x), word 2 0 0, x * word 2 0 0, x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0],
      rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
    rw [word_gen]
    simp only [rowName, Bool.false_eq_true, ↓reduceIte] at hnext
    exact ⟨hcall, l11, l13, l14, l7, l8, hk, hnext⟩
  · simp only [Fn.SemB, rowBody, ↓reduceIte, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB,
      List.map_cons, List.map_nil]
    obtain ⟨d0, d1, s, R, a, hcall, l11, l13, l14, h7, hP⟩ := h
    obtain ⟨l7, l8⟩ := cellsAt_two.mp h7
    obtain ⟨P, l18, h7'⟩ := hP rfl
    obtain ⟨l7', l8'⟩ := cellsAt_two.mp h7'
    refine ⟨listVal [x, W, lv, rb, xb, node, pb, d0, d1, s, rb * x, R, R * xb, a, a + s, x * x,
      node * (x * x), pb * x, P, xb * xb, P * (xb * xb), word 2 0 0, x * word 2 0 0,
      x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
    rw [word_gen]
    simp only [rowName, ↓reduceIte] at hnext
    exact ⟨hcall, l11, l13, l14, l7, l8, l18, l7', l8', hk, hnext, trivial⟩

/-- **The row loop over a completeness model**, from `1` (`row_loop_meaning`'s backward half). -/
theorem row_loop_comp {CM : CompModel} (store : Bool) (rd : Reader) (W lv rb xb node pb : E)
    (h : LoopTo W fun j => RowCellM CM.hm store rd lv rb xb node pb (gen ^ j)) :
    coreProgram.RelB CM.sem rd (rowName store) [1, W, lv, rb, xb, node, pb] [] := by
  obtain ⟨m, hm, hW, -, hall⟩ := h
  have := loopB_bwd (k := 0) (S := CM.sem) (rd := rd)
    (B := fun x => RowStep store rd lv rb xb node pb (coreProgram.RelB CM.sem rd) x)
    (fun x hB hK hn => row_step_bwdB store rd W lv rb xb node pb x hB hK hn) hm hW
    (fun j _ hj => by
      obtain ⟨d0, d1, s, R, a, hcall, h1, h2, h3, h4, h5⟩ := hall j hj
      exact ⟨d0, d1, s, R, a, da_verify_cell_comp hcall, h1, h2, h3, h4, h5⟩)
  rwa [pow_zero] at this

/-- **The gap loop under any semantics**, from `1` (free of `BLAKE2S`). -/
theorem gap_loop_compB {S : BlakeSem} (store : Bool) (rd : Reader) (W node nb : E)
    (h : LoopTo W fun j => GapStep rd node nb (gen ^ j)) :
    coreProgram.RelB S rd (gapName store) [1, W, node, nb] [] := by
  rw [relB_iff_rel_of_freeOn (S := S) freeOn_gap (by cases store <;> simp [gapName])]
  exact (gap_loop_meaning store rd W node nb).mpr h

/-- The tree dispatch on `g^k`, `k < 11`, over a completeness model. -/
theorem dl_dispatch_comp {CM : CompModel} {rd : Reader} {glp node c0 c1 : E}
    (h : ∃ k < 11, glp = gen ^ k ∧ Meaning_da_levelsWith CM.hm k rd [node] [c0, c1]) :
    ∃ (j : ℕ) (h : j < dlNames.length), glp = ofK (gpow j) ∧
      coreProgram.RelB CM.sem rd dlNames[j] [node] [c0, c1] := by
  obtain ⟨k, hk, hg, hm⟩ := h
  refine ⟨k, by rw [dlNames_length]; exact hk, by rw [hg, gen_pow_eq_ofK], ?_⟩
  rw [← List.getD_eq_getElem _ ""]
  exact da_levels_comp k (by omega) _ _ hm

/-- **`da_verify_column__L{store}` over a completeness model** (`Meaning_da_verify_column`, the
cells and the tree over the model's answers, the vector hash's rows under its semantics). -/
def Meaning_da_verify_columnComp (CM : CompModel) (store : Bool) (rd : Reader)
    (args rets : List E) : Prop :=
  ∃ xb nb np gap glp pb ct rb hs ctr, args = [xb, nb, np, gap, glp, pb, ct, rb, hs, ctr] ∧
    rets = [] ∧ ∃ h0 h1 o0 o1 lv node c0 c1,
      CellsAt rd (hs * (xb * xb)) [h0, h1] ∧
      Meaning_da_vector_dispatchB CM.sem rd [xb, h0, h1, ctr] [o0, o1, lv] ∧
      CellsAt rd (hs * (xb * gen * (xb * gen))) [o0, o1] ∧
      IsInK nb ∧ (nb ≠ 1 → LoopTo nb fun j => RowCellM CM.hm store rd lv rb xb node pb (gen ^ j)) ∧
      IsInK gap ∧ (gap ≠ 1 → LoopTo gap fun j => GapStep rd node nb (gen ^ j)) ∧
      (∃ k < 11, glp = gen ^ k ∧ Meaning_da_levelsWith CM.hm k rd [node] [c0, c1]) ∧
      CellsAt rd (ct * (xb * xb)) [c0, c1]

/-- **`da_verify_column__L{store}` is complete over a completeness model.** -/
theorem da_verify_column_comp {CM : CompModel} (store : Bool) (rd : Reader) (args rets : List E)
    (h : Meaning_da_verify_columnComp CM store rd args rets) :
    coreProgram.RelB CM.sem rd (colName store) args rets := by
  rw [relB_of_find (find_col store)]
  simp only [Fn.SemB, colBody, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil, true_and, word_one, word_gen]
  obtain ⟨xb, nb, np, gap, glp, pb, ct, rb, hs, ctr, rfl, rfl, h0, h1, o0, o1, lv, node, c0, c1,
    h12, hdisp, h14, hk1, hrow, hk3, hgap, hdl, h30⟩ := h
  obtain ⟨l12, l13⟩ := cellsAt_two.mp h12
  obtain ⟨l14, l15⟩ := cellsAt_two.mp h14
  obtain ⟨l30, l31⟩ := cellsAt_two.mp h30
  refine ⟨listVal [xb, nb, np, gap, glp, pb, ct, rb, hs, ctr, xb * xb, hs * (xb * xb), h0, h1, o0,
    o1, lv, gen, xb * gen, xb * gen * (xb * gen), hs * (xb * gen * (xb * gen)), np * np,
    np * np * (np * np), node, 1, 1 + nb, 1, 1, 1 + gap, 1, c0, c1, xb * xb, ct * (xb * xb)],
    rfl, ?_⟩
  simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and, and_true]
  exact ⟨l12, l13, da_vector_dispatch_compB hdisp, l14, l15, isInK_one_add.mpr hk1,
    fun h => row_loop_comp store rd _ _ _ _ _ _ (hrow (one_add_ne_zero.mp h)),
    isInK_one_add.mpr hk3, fun h => gap_loop_compB store rd _ _ _ (hgap (one_add_ne_zero.mp h)),
    dl_dispatch_comp hdl, l30, l31⟩

/-! ## At the deployed model -/

theorem meaning_da_vector_cellB_of_deployed {final : Bool} {rd : Reader} {args rets : List E}
    (h : Meaning_da_vector_cell final rd args rets) :
    Meaning_da_vector_cellB blakeDeployed final rd args rets := by
  obtain ⟨xb, h0, h1, ctr, o0, o1, wp, ha, hr, ws, cv, hwl, hcl, hcv, hch, hfr⟩ := h
  refine ⟨xb, h0, h1, ctr, o0, o1, wp, ha, hr, ws, cv, hwl, hcl, hcv, ?_, hfr⟩
  rcases hch with ⟨h96, -⟩ | ⟨-, hd, hst0, hcan, hout⟩
  · omega
  · exact ⟨fun i => digestScalars (chainRun hd (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0)) i),
      hst0.symm, hout.symm, steps_of_chainCells hcan⟩

theorem meaning_da_verify_columnComp_of_deployed {store : Bool} {rd : Reader} {args rets : List E}
    (h : Meaning_da_verify_column store rd args rets) :
    Meaning_da_verify_columnComp CompModel.deployed store rd args rets := by
  obtain ⟨xb, nb, np, gap, glp, pb, ct, rb, hs, ctr, ha, hr, h0, h1, o0, o1, lv, node, c0, c1,
    h12, hdisp, h14, hk1, hrow, hk3, hgap, ⟨k, hk, hg, hdl⟩, h30⟩ := h
  obtain ⟨x0, rest, hx, hK, hM⟩ := hdisp
  refine ⟨xb, nb, np, gap, glp, pb, ct, rb, hs, ctr, ha, hr, h0, h1, o0, o1, lv, node, c0, c1,
    h12, ⟨x0, rest, hx, hK, meaning_da_vector_cellB_of_deployed hM⟩, h14, hk1, fun hn => ?_, hk3,
    hgap, ⟨k, hk, hg, meaning_da_levelsWith_of_deployed hdl⟩, h30⟩
  obtain ⟨m, hm, hW, hfirst, hall⟩ := hrow hn
  refine ⟨m, hm, hW, hfirst, fun j hj => ?_⟩
  obtain ⟨d0, d1, s, R, a, hcall, r1, r2, r3, r4, r5⟩ := hall j hj
  exact ⟨d0, d1, s, R, a, meaning_da_verify_cellWith_deployed.mpr hcall, r1, r2, r3, r4, r5⟩

theorem da_verify_column_of_comp (store : Bool) (rd : Reader) (args rets : List E)
    (h : Meaning_da_verify_column store rd args rets) :
    coreProgram.Rel rd (colName store) args rets := by
  rw [← relB_deployed]
  exact da_verify_column_comp (CM := CompModel.deployed) store rd args rets
    (meaning_da_verify_columnComp_of_deployed h)

end
end LeanVM.Guest.B1.Digest
