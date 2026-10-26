/-
  LeanVM.Prover.WitnessStack

  The executable stack is the specification's: the committed columns end to end in the stacking
  order, zeros after, is `stackOf`.
-/

module

public import LeanVM.Prover.WitnessColumns

/-!
# The stack

`stackOrderOf_pyKappas`: the executable stacking order, from the Python's column log-sizes, is
the instance's (`stackOrder`) by Python number. `stackArray_eq`: the columns laid end to end in
that order, then zeros up to `2^μ`, are `stackOf`, given each committed column's array is the
witness's column: the blocks' offsets are the sums of the heights before them
(`offsetNat_eq`), so a cell in a block's window is that block's cell (`getElem_flatten_offset`,
`stackAt_getElem_of_inWindow`), and past the total both are zero.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Verifier
open Air.Flat (EnsembleWitness)

@[expose] public section

/-! ## Lists laid end to end -/

/-- Appending arrays in a fold is flattening their lists. -/
theorem foldl_append_toList {α : Type} (f : ℕ → Array α) :
    ∀ (l : List ℕ) (a : Array α),
      (l.foldl (fun acc c ↦ acc ++ f c) a).toList = a.toList ++ (l.map fun c ↦ (f c).toList).flatten
  | [], a => by simp
  | c :: l, a => by
    rw [List.foldl_cons, foldl_append_toList f l, Array.toList_append, List.map_cons,
      List.flatten_cons, List.append_assoc]

/-- An entry of lists laid end to end: entry `y` of list `b` sits past the lengths of the lists
before it. -/
theorem getElem?_flatten_offset {α : Type} :
    ∀ (Ls : List (List α)) (b : ℕ) (hb : b < Ls.length) (y : ℕ) (hy : y < Ls[b].length),
      Ls.flatten[((Ls.take b).map List.length).sum + y]? = some Ls[b][y]
  | [], _, hb, _, _ => absurd hb (by simp)
  | L :: Ls, 0, _, y, hy => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons]
    rw [List.getElem?_append_left (show y < L.length from hy)]
    simp
  | L :: Ls, b + 1, hb, y, hy => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons]
    rw [Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact getElem?_flatten_offset Ls b (by simpa using hb) y hy

/-! ## The stacking order -/

/-- **The executable stacking order is the instance's**, by Python number. -/
theorem stackOrderOf_pyKappas (prog : Program) (s : Sizes) :
    stackOrderOf (pyKappas prog s) = (stackOrder prog s).map pyCol := by
  unfold stackOrderOf
  have hb : blockColumns = committedColumns.map pyCol := blockCols_eq
  simp only [hb, List.length_map, blockSizes_eq]
  rw [order_eq, List.map_map]
  refine List.map_congr_left fun c hc ↦ ?_
  have hmem : c ∈ committedColumns := List.mem_mergeSort.mp hc
  have hlt : committedColumns.idxOf c < (committedColumns.map pyCol).length := by
    rw [List.length_map]; exact List.idxOf_lt_length_of_mem hmem
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_idxOf]

/-- The executable stack's log-size is the instance's `μ`. -/
theorem placementsOf_snd (prog : Program) (s : Sizes) :
    (placementsOf (pyKappas prog s)).2 = leanIsaμ prog s :=
  stackLog_verifierLayout prog s

/-! ## The stack -/

variable {prog : Program} (s : Sizes) (w : EnsembleWitness (leanIsaEnsemble prog))

/-- The stacked total is the heights of the committed columns in stacking order. -/
theorem total_eq_sum_stackOrder :
    (blocks prog s).total = ((stackOrder prog s).map fun c ↦ 2 ^ kappa prog s c).sum := by
  rw [Blocks.total, offsetNat_eq prog s _ le_rfl, List.take_of_length_le (by simp [blocks])]

/-- **The stack, laid end to end.** Given each committed column's array, at its Python number,
is the witness's column, the columns laid end to end in the stacking order, then zeros up to
`2^μ`, are the stack of the witness. -/
theorem stackArray_eq (cols : Array (Array K))
    (hcols : ∀ c ∈ stackOrder prog s, cols.getD (pyCol c) #[] = (witnessColumn prog s w c).toArray) :
    stackArray (leanIsaμ prog s) cols ((stackOrder prog s).map pyCol) =
      (stackOf prog s w).values.toArray := by
  unfold stackArray
  simp only
  set a := ((stackOrder prog s).map pyCol).foldl (fun acc c ↦ acc ++ cols.getD c #[])
    (Array.emptyWithCapacity (2 ^ leanIsaμ prog s)) with ha
  set Ls : List (List K) := (stackOrder prog s).map fun c ↦ (witnessColumn prog s w c).toList
    with hLs
  have hlen : ∀ (b : ℕ) (hb : b < Ls.length),
      Ls[b].length = 2 ^ kappa prog s ((stackOrder prog s)[b]'(by simpa [hLs] using hb)) := by
    intro b hb
    simp [hLs]
  have hfold : a.toList = Ls.flatten := by
    rw [ha, foldl_append_toList, List.map_map]
    simp only [Array.emptyWithCapacity_eq, Array.toList_empty, List.nil_append, hLs]
    congr 1
    refine List.map_congr_left fun c hc ↦ ?_
    simp only [Function.comp_apply, hcols c hc, Vector.toList_toArray]
  have hsumtake : ∀ b ≤ (stackOrder prog s).length,
      ((Ls.take b).map List.length).sum = (blocks prog s).offsetNat b := by
    intro b hb
    rw [offsetNat_eq prog s b (by simpa [blocks] using hb), hLs, ← List.map_take, List.map_map]
    congr 1
    refine List.map_congr_left fun c _ ↦ ?_
    simp
  have htotal : Ls.flatten.length = (blocks prog s).total := by
    rw [List.length_flatten, total_eq_sum_stackOrder, hLs, List.map_map]
    congr 1
    refine List.map_congr_left fun c _ ↦ ?_
    simp
  have hasize : a.size = (blocks prog s).total := by
    rw [← Array.length_toList, hfold, htotal]
  have hfits := blocks_fits prog s
  apply Array.ext
  · simp only [Array.size_append, Array.size_replicate, Vector.size_toArray, hasize]
    omega
  · intro x h1 h2
    have hx : x < 2 ^ leanIsaμ prog s := by simpa using h2
    rw [Vector.getElem_toArray]
    show _ = ((blocks prog s).stackAt (fun b ↦ witnessColumn prog s w (stackOrder prog s)[b])
      (leanIsaμ prog s) 0)[x]
    by_cases hxt : x < (blocks prog s).total
    · obtain ⟨b, hb⟩ := (blocks prog s).exists_inWindow hxt
      refine Eq.trans ?_ (Blocks.stackAt_getElem_of_inWindow _ _ _ hx hb).symm
      have hsz : x < a.size := by rw [hasize]; exact hxt
      rw [Array.getElem_append_left hsz]
      have hbL : b.val < Ls.length := by simpa [hLs, blocks] using b.isLt
      have hy : x - (blocks prog s).offset b < Ls[b.val].length := by
        rw [hlen b.val hbL]
        have h2 := hb.2
        have h1 := hb.1
        change x < (blocks prog s).offset b + 2 ^ kappa prog s ((stackOrder prog s)[b.val]) at h2
        omega
      have e := getElem?_flatten_offset Ls b.val hbL (x - (blocks prog s).offset b) hy
      rw [hsumtake b.val (by simpa [blocks] using b.isLt.le), ← Blocks.offset,
        Nat.add_sub_cancel' hb.1, ← hfold, Array.getElem?_toList,
        Array.getElem?_eq_getElem hsz] at e
      refine (Option.some_inj.mp e).trans ?_
      simp only [hLs, List.getElem_map, Vector.getElem_toList]
      rfl
    · refine Eq.trans ?_ (Blocks.stackAt_getElem_of_total_le _ _ _ hx (Nat.le_of_not_lt hxt)).symm
      rw [Array.getElem_append_right (by rw [hasize]; omega)]
      simp

end

end LeanVM.Prover
