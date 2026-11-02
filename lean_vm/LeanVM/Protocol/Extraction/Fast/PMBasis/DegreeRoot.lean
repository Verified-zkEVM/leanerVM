module

public import LeanVM.Protocol.Extraction.Fast.PMBasis.DegreeRecursion

/-!
# The PM-basis root pass: `r` rows, weak Popov, shifted degrees kept

`pmBasisNormalizeRoot problem shift basis` (CompPoly's `Approximant/PMBasis/Recursion.lean`) runs
the pivot-table reduction once over the recursion's basis (`reduceKernelLeafRows`, the leaf's
`reduceKernelLeafRowsByPivots` at the fuel `reduceKernelLeafFuel`), drops zero rows and completes
the missing leading positions by `X^cap·eᵢ` (`cap = leafDegreeCap problem = max 1 (maxOrder
problem)`). What it does, at any input of rows of width `m = problem.matrix.size`:

* it returns exactly `m` rows, nonzero, with pairwise distinct shifted leading positions, so
  shifted weak Popov (**`pmBasisNormalizeRoot_shape`**), whatever the fuel: a row the fuel drops is
  replaced by a completion row;
* its cancellations never raise a row's shifted degree beyond the table's (a cancellation of a
  target by a reducer of no larger shifted degree at the same position subtracts `c·X^Δ·reducer`,
  of shifted degree `Δ + rdeg_s(reducer) = rdeg_s(target)`), so every row it returns is either
  bounded entrywise like its input, `deg(entryⱼ) + sⱼ ≤ D`, or a completion row
  (**`pmBasisNormalizeRoot_rows`**);
* on the kernel-leaf recursion at `leafCutoff ≤ 1` (degree at most `max 1 o`, `DegreeRecursion`),
  every entry of `pmBasis`'s rows has `deg(entryⱼ) + sⱼ ≤ max 1 o + max s`
  (**`pmBasis_entry_le`**). Degree at most the order itself is not kept in general: a reducer
  leading at a position of larger shift brings `X^Δ·(entries of degree up to o)` into columns of
  smaller shift. When the recursion's output is already shifted weak Popov with distinct leading
  positions (the plan's change (d), track popov), the pass cancels nothing.

Its cost is not bounded here: a full pass inserts every row into the table, a conflict costing
`O(m)` entry updates of degree up to `D`, the number of conflicts bounded only by the fuel
`(rows + 1)·(m + 1)·(D + 1)`, `D` the largest shifted row degree (shifts included).

Credits: the root pass and the lemmas used here are CompPoly's
(github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly Contributors";
`LinearAlgebra/PolynomialMatrix/`, Valerii Huhnin).
-/

namespace LeanVM.Extraction.Fast.PMDegree

open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open DenseMatrix (array_getD_of_lt' array_getD_of_le')

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Every nonzero entry `j` of `row` has `deg + shift[j] ≤ D` (shifted row degree at most `D`). -/
@[expose] def EntryBound (D : Nat) (shift : Array Nat) (row : PolynomialRow F) : Prop :=
  ∀ j, rowGet row j ≠ 0 → (rowGet row j).natDegree + shift.getD j 0 ≤ D

theorem natDegree_polynomialScaleCoeffX_le (c : F) (d : Nat) (p : CPolynomial F) :
    (polynomialScaleCoeffX c d p).natDegree ≤ d + p.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly, polynomialScaleCoeffX_toPoly]
  exact Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add_right (Polynomial.natDegree_C_mul_X_pow_le c d) _)

/-- A cancellation of a target by a reducer of no larger shifted degree keeps the target's entrywise
shifted degree bound (the reducer's entries are bounded by its shifted degree). -/
theorem entryBound_cancel {D : Nat} {shift : Array Nat} {target reducer : PolynomialRow F}
    (ht : EntryBound D shift target)
    (hle : ∀ t r, rowShiftedLeadingTerm? target shift = some t →
      rowShiftedLeadingTerm? reducer shift = some r → r.shiftedDegree ≤ t.shiftedDegree) :
    EntryBound D shift (cancelKernelLeafLeadingTerm target reducer shift) := by
  cases htt : rowShiftedLeadingTerm? target shift with
  | none =>
      simp only [cancelKernelLeafLeadingTerm, htt]
      exact ht
  | some t =>
      cases hrr : rowShiftedLeadingTerm? reducer shift with
      | none =>
          simp only [cancelKernelLeafLeadingTerm, htt, hrr]
          exact ht
      | some r =>
          have hlt := hle t r htt hrr
          obtain ⟨_, _, htne, htdeg, htsdeg, _⟩ := rowShiftedLeadingTerm?_some_data htt
          obtain ⟨hrsd, _, _, _, hrsdeg, _⟩ := rowShiftedLeadingTerm?_some_data hrr
          simp only [cancelKernelLeafLeadingTerm, htt, hrr]
          split_ifs with hpos hc
          · exact ht
          · have hpos' : t.position = r.position := beq_iff_eq.mp hpos
            have htD : t.shiftedDegree ≤ D := by
              have := ht _ htne
              rw [← htdeg] at this
              omega
            have hΔ : (t.degree - r.degree) + r.shiftedDegree = t.shiftedDegree := by
              rw [hpos'] at htsdeg
              omega
            intro j hj
            rw [rowGet_rowSub, rowGet_rowScaleCoeffX'] at hj ⊢
            set a := rowGet target j with ha
            set b := rowGet reducer j with hb
            set P := polynomialScaleCoeffX (t.coeff / r.coeff) (t.degree - r.degree) b with hP
            have hA : a ≠ 0 → a.natDegree + shift.getD j 0 ≤ D := ht j
            have hPb : P ≠ 0 → P.natDegree + shift.getD j 0 ≤ D := by
              intro hPne
              have hbne : b ≠ 0 := by
                rintro hb0
                apply hPne
                rw [hP, hb0, polynomialScaleCoeffX_zero']
              have hjsize : j < reducer.size := by
                by_contra hcon
                exact hbne (rowGet_of_size_le (Nat.le_of_not_lt hcon))
              have hbr := rowShiftedDegree?_entry_bound hrsd hjsize hbne
              rw [← hb] at hbr
              have hPdeg := natDegree_polynomialScaleCoeffX_le (t.coeff / r.coeff)
                (t.degree - r.degree) b
              rw [← hP] at hPdeg
              omega
            by_cases ha0 : a = 0
            · have hPne : P ≠ 0 := by
                intro hP0
                apply hj
                rw [ha0, hP0, sub_zero]
              rw [ha0, zero_sub, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_neg,
                Polynomial.natDegree_neg, ← CPolynomial.natDegree_toPoly]
              exact hPb hPne
            · by_cases hP0 : P = 0
              · rw [hP0, sub_zero]
                exact hA ha0
              · have hsub := CPolynomial.natDegree_sub_le a P
                have h1 := hA ha0
                have h2 := hPb hP0
                omega
          · exact ht

theorem entryBound_cancelClosed (D : Nat) (shift : Array Nat) :
    CancelClosed (F := F) (EntryBound D shift) shift :=
  fun _ _ ht _ hle ↦ entryBound_cancel ht hle

omit [LawfulBEq F] in
theorem replicate_none_inv {n : Nat} (shift : Array Nat) (w : Nat) :
    ∀ p r, (Array.replicate w (none : Option (PolynomialRow F))).getD p none = some r →
      r.size = n ∧ rowShiftedLeadingPosition? r shift = some p := by
  intro p r hget
  rcases Nat.lt_or_ge p (Array.replicate w (none : Option (PolynomialRow F))).size with hp | hp
  · rw [array_getD_of_lt' _ _ hp, Array.getElem_replicate] at hget
    cases hget
  · rw [array_getD_of_le' _ _ hp] at hget
    cases hget

/-- **The root pass returns exactly `m` rows**, nonzero, with pairwise distinct shifted leading
positions (so shifted weak Popov), when its input rows have width `m`. -/
theorem pmBasisNormalizeRoot_shape (problem : XAdicProblem F) (shift : Array Nat)
    (basis : PolynomialMatrix F)
    (hsizes : ∀ r ∈ MatrixRows basis, r.size = problem.matrix.size) :
    (pmBasisNormalizeRoot problem shift basis).size = problem.matrix.size ∧
      PivotShape problem.matrix.size shift (pmBasisNormalizeRoot problem shift basis) := by
  rw [pmBasisNormalizeRoot]
  refine completeMissingPivotRows_shape problem shift ?_
  rw [compactNonzeroRows]
  refine PivotShape.filter ?_ _
  rw [reduceKernelLeafRows, reduceKernelLeafRowsByPivots, ← Array.foldl_toList]
  exact pivotShape_pivotRows (insertKernelLeaf_foldl_pivotInv _ _ _ shift
    (fun r hr ↦ hsizes r hr) (replicate_none_inv shift _))

/-- **The root pass keeps an entrywise shifted degree bound**: each row it returns is bounded like
its input rows, or is a completion row `X^cap·eᵢ`. -/
theorem pmBasisNormalizeRoot_rows (problem : XAdicProblem F) (shift : Array Nat)
    (basis : PolynomialMatrix F) {D : Nat}
    (hD : ∀ r ∈ MatrixRows basis, EntryBound D shift r) :
    ∀ r ∈ MatrixRows (pmBasisNormalizeRoot problem shift basis),
      EntryBound D shift r ∨ ∃ i, i < problem.matrix.size ∧
        r = monomialUnitRow problem.matrix.size i (leafDegreeCap problem) := by
  intro r hr
  rw [pmBasisNormalizeRoot, MatrixRows, completeMissingPivotRows, Array.toList_append] at hr
  rcases List.mem_append.mp hr with hr | hr
  · left
    have hr' := compactNonzeroRows_subset (rows := reduceKernelLeafRows basis shift) hr
    rw [reduceKernelLeafRows] at hr'
    exact reduceKernelLeafRowsByPivots_invariant' _ shift (entryBound_cancelClosed D shift) hD hr'
  · right
    rw [missingCompletionRows, List.toList_toArray] at hr
    rcases List.mem_filterMap.mp hr with ⟨i, hi, hsome⟩
    split at hsome
    · cases hsome
    · cases hsome
      exact ⟨i, List.mem_range.mp hi, rfl⟩

omit [Field F] [BEq F] [LawfulBEq F] in
theorem le_foldl_max : ∀ (l : List Nat) (acc x : Nat), (x ∈ l ∨ x ≤ acc) → x ≤ l.foldl max acc := by
  intro l
  induction l with
  | nil =>
      intro acc x hx
      rcases hx with hx | hx
      · cases hx
      · exact hx
  | cons a l ih =>
      intro acc x hx
      rw [List.foldl_cons]
      refine ih _ x ?_
      rcases hx with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Nat.le_max_right _ _)
        · exact Or.inl hx
      · exact Or.inr (hx.trans (Nat.le_max_left _ _))

omit [Field F] [BEq F] [LawfulBEq F] in
theorem getD_le_foldl_max (a : Array Nat) (j : Nat) : a.getD j 0 ≤ a.foldl max 0 := by
  rw [← Array.foldl_toList]
  rcases Nat.lt_or_ge j a.size with hj | hj
  · refine le_foldl_max _ _ _ (Or.inl ?_)
    rw [array_getD_of_lt' _ _ hj]
    exact Array.getElem_mem_toList hj
  · rw [array_getD_of_le' _ _ hj]
    exact Nat.zero_le _

/-- **`pmBasis` on the kernel-leaf runtime at `leafCutoff ≤ 1`**: exactly `m` rows of width `m`,
shifted weak Popov, every nonzero entry `j` with `deg + sⱼ ≤ max 1 (maxOrder problem) + max s`. -/
theorem pmBasis_entry_le (mulCtx : CPolynomial.MulContext F) (lowCtx : MulLowContext F)
    {leafCutoff : Nat} (composeLeafCutoff : Nat) (hcut : leafCutoff ≤ 1)
    (problem : XAdicProblem F) (shift : Array Nat) :
    let B := pmBasis (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
      composeLeafCutoff) problem shift
    B.size = problem.matrix.size ∧ PivotShape problem.matrix.size shift B ∧
      ShiftedWeakPopov B shift ∧
      ∀ r ∈ MatrixRows B, ∀ j, rowGet r j ≠ 0 →
        (rowGet r j).natDegree + shift.getD j 0 ≤ max 1 (maxOrder problem) + shift.foldl max 0 := by
  intro B
  set core := pmBasisWithFuelCore (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
    composeLeafCutoff) (pmBasisFuel problem) problem shift with hcore
  have hB : B = pmBasisNormalizeRoot problem shift core := rfl
  have hsizes : ∀ r ∈ MatrixRows core, r.size = problem.matrix.size := fun r hr ↦
    (pmBasisWithFuelCore_kernelLeaf_rows mulCtx lowCtx leafCutoff composeLeafCutoff _ problem
      shift r hr).2
  obtain ⟨hsize, hshape⟩ := pmBasisNormalizeRoot_shape problem shift core hsizes
  rw [← hB] at hsize hshape
  refine ⟨hsize, hshape, hshape.shiftedWeakPopov, fun r hr j hj ↦ ?_⟩
  have hS := getD_le_foldl_max shift j
  have hD : ∀ r ∈ MatrixRows core, EntryBound (max 1 (maxOrder problem) + shift.foldl max 0)
      shift r := by
    intro r hr j _
    have := pmBasisCore_natDegree_le mulCtx lowCtx composeLeafCutoff hcut problem shift r hr j
    have := getD_le_foldl_max shift j
    omega
  rw [hB] at hr
  rcases pmBasisNormalizeRoot_rows problem shift core hD r hr with h | ⟨i, _hi, rfl⟩
  · exact h j hj
  · have hdeg : (rowGet (monomialUnitRow (F := F) problem.matrix.size i
        (leafDegreeCap problem)) j).natDegree ≤ leafDegreeCap problem :=
      (homRow_monomialUnitRow _ _ _).natDegree_le j
    have hcap : leafDegreeCap problem = max 1 (maxOrder problem) := rfl
    omega

end

end LeanVM.Extraction.Fast.PMDegree
