module

public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.Correctness

/-!
# The PM-basis kernel leaf at order one: `r` rows, weak Popov, degree at most one

CompPoly's PM-basis (`pmBasisWithFuelCore`, `Approximant/PMBasis/Recursion.lean`) ends its
recursion in the scalar-kernel leaf `kernelLeafBasis` (`Approximant/PMBasis/KernelLeaf.lean`): the
kernel of the order-`cap` coefficient matrix (`cap = leafDegreeCap = max 1 (maxOrder problem)`),
read back as polynomial rows of degree `< cap`, together with the rows `X^cap·eᵢ`, reduced one row
at a time into a pivot table indexed by shifted leading position (`insertKernelLeafPivotRowWithFuel`,
whose cancellation `cancelKernelLeafLeadingTerm` subtracts `c·X^Δ·pivot`), and completed by
`X^cap·eᵢ` for the positions no reduced row holds (`completeMissingPivotRows`).

At any cap the leaf returns exactly `r = problem.matrix.size` rows, each of width `r`, nonzero,
with pairwise distinct shifted leading positions (**`kernelLeafBasis_shape`**): the pivot table
holds one row per position it fills, and the completion fills the others. At cap one
(`maxOrder problem ≤ 1`: what the recursion hands its leaves when `leafCutoff ≤ 1` and the fuel
suffices, `DegreeRecursion.lean`) every row is moreover `X^e·v` for a constant vector `v` and
`e ≤ 1` (**`kernelLeafBasis_homRowLe_one`**), so every entry has degree at most one
(**`kernelLeafBasis_natDegree_le_one`**): the kernel vectors are constant rows, the completions are
`X·eᵢ`, and a cancellation of `X^a·u` by `X^b·w` at a common leading position happens only when
`b ≤ a` (the reducer's shifted degree is at most the target's, at the same position, hence the same
shift), giving `X^a·(u − c·w)`. A cancellation with `b > a` would truncate `Δ = a − b` to `0` and
mix degrees; it never happens, but CompPoly's invariant lemmas
(`reduceKernelLeafRowsIncremental_invariant`) ask for closure under every cancellation, so the
pivot-table invariant is proved again here for predicates closed under the cancellations the table
performs (`insertPivot_invariant`, `reduceKernelLeafRowsIncremental_invariant'`).

Credits: the leaf, its pivot table and CompPoly's lemmas used here are CompPoly's
(github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly Contributors";
`LinearAlgebra/PolynomialMatrix/Approximant/PMBasis/`, Valerii Huhnin). The proofs of
`insertPivot_invariant` and its folds, and of the monomial unit rows' leading positions, follow
CompPoly's private ones (`KernelLeafSoundness.lean`, `Correctness.lean`).
-/

namespace LeanVM.Extraction.Fast.PMDegree

open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open DenseMatrix (array_getD_of_lt' array_getD_of_le' array_getD_setIfInBounds)

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## Homogeneous rows -/

/-- Every entry of `row` is `a·X^e` (the zero entries with `a = 0`). -/
def HomRow (e : Nat) (row : PolynomialRow F) : Prop :=
  ∀ j, ∃ a : F, (rowGet row j).toPoly = Polynomial.C a * Polynomial.X ^ e

/-- `row` is homogeneous of some degree `e ≤ B`. -/
def HomRowLe (B : Nat) (row : PolynomialRow F) : Prop :=
  ∃ e, e ≤ B ∧ HomRow e row

theorem HomRow.natDegree_le {e : Nat} {row : PolynomialRow F} (h : HomRow e row) (j : Nat) :
    (rowGet row j).natDegree ≤ e := by
  obtain ⟨a, ha⟩ := h j
  rw [CPolynomial.natDegree_toPoly, ha]
  exact Polynomial.natDegree_C_mul_X_pow_le a e

theorem HomRow.natDegree_eq {e : Nat} {row : PolynomialRow F} (h : HomRow e row) {j : Nat}
    (hne : rowGet row j ≠ 0) : (rowGet row j).natDegree = e := by
  obtain ⟨a, ha⟩ := h j
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hne
    rw [← CPolynomial.toPoly_eq_zero_iff, ha, map_zero, zero_mul]
  rw [CPolynomial.natDegree_toPoly, ha, Polynomial.natDegree_C_mul_X_pow e a ha0]

theorem HomRowLe.natDegree_le {B : Nat} {row : PolynomialRow F} (h : HomRowLe B row) (j : Nat) :
    (rowGet row j).natDegree ≤ B := by
  obtain ⟨e, he, hrow⟩ := h
  exact (hrow.natDegree_le j).trans he

/-- A polynomial whose coefficients vanish off degree `e` is `c·X^e`. -/
theorem toPoly_eq_C_mul_X_pow_of_coeff {p : CPolynomial F} {e : Nat}
    (h : ∀ k, k ≠ e → p.coeff k = 0) :
    p.toPoly = Polynomial.C (p.coeff e) * Polynomial.X ^ e := by
  ext n
  rw [Polynomial.coeff_C_mul_X_pow, ← CPolynomial.coeff_toPoly]
  by_cases hn : n = e
  · rw [ite_eq_left hn, hn]
  · rw [ite_eq_right hn, h n hn]

theorem polynomialScaleCoeffX_zero' (c : F) (d : Nat) :
    polynomialScaleCoeffX c d (0 : CPolynomial F) = 0 := by
  rw [← CPolynomial.toPoly_eq_zero_iff, polynomialScaleCoeffX_toPoly, CPolynomial.toPoly_zero,
    mul_zero]

theorem rowGet_rowScaleCoeffX' (c : F) (d : Nat) (row : PolynomialRow F) (j : Nat) :
    rowGet (rowScaleCoeffX c d row) j = polynomialScaleCoeffX c d (rowGet row j) := by
  rcases Nat.lt_or_ge j row.size with hj | hj
  · rw [rowScaleCoeffX, rowGet, rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    rfl
  · rw [rowGet, rowGet, array_getD_of_le' _ _ (by rw [rowScaleCoeffX_size]; exact hj),
      array_getD_of_le' _ _ hj, polynomialScaleCoeffX_zero']

/-- A cancellation of a homogeneous row by a homogeneous row of no larger shifted degree keeps it
homogeneous, of the target's degree. -/
theorem homRowLe_cancel {B : Nat} {target reducer : PolynomialRow F} {shift : Array Nat}
    (ht : HomRowLe B target) (hr : HomRowLe B reducer)
    (hle : ∀ t r, rowShiftedLeadingTerm? target shift = some t →
      rowShiftedLeadingTerm? reducer shift = some r → r.shiftedDegree ≤ t.shiftedDegree) :
    HomRowLe B (cancelKernelLeafLeadingTerm target reducer shift) := by
  obtain ⟨et, het, hT⟩ := ht
  obtain ⟨er, her, hR⟩ := hr
  cases htt : rowShiftedLeadingTerm? target shift with
  | none =>
      simp only [cancelKernelLeafLeadingTerm, htt]
      exact ⟨et, het, hT⟩
  | some t =>
      cases hrr : rowShiftedLeadingTerm? reducer shift with
      | none =>
          simp only [cancelKernelLeafLeadingTerm, htt, hrr]
          exact ⟨et, het, hT⟩
      | some r =>
          have hlt := hle t r htt hrr
          obtain ⟨_, _, htne, htdeg, htsdeg, _⟩ := rowShiftedLeadingTerm?_some_data htt
          obtain ⟨_, _, hrne, hrdeg, hrsdeg, _⟩ := rowShiftedLeadingTerm?_some_data hrr
          simp only [cancelKernelLeafLeadingTerm, htt, hrr]
          split_ifs with hpos hc
          · exact ⟨et, het, hT⟩
          · have hpos' : t.position = r.position := beq_iff_eq.mp hpos
            have het' : t.degree = et := by rw [htdeg]; exact hT.natDegree_eq htne
            have her' : r.degree = er := by rw [hrdeg]; exact hR.natDegree_eq hrne
            have hle' : er ≤ et := by rw [hpos'] at htsdeg; omega
            refine ⟨et, het, fun j ↦ ?_⟩
            obtain ⟨a, ha⟩ := hT j
            obtain ⟨b, hb⟩ := hR j
            refine ⟨a - t.coeff / r.coeff * b, ?_⟩
            rw [rowGet_rowSub, rowGet_rowScaleCoeffX', CPolynomial.toPoly_sub,
              polynomialScaleCoeffX_toPoly, ha, hb, het', her']
            obtain ⟨k, rfl⟩ : ∃ k, et = er + k := ⟨et - er, by omega⟩
            rw [Nat.add_sub_cancel_left, map_sub, map_mul, pow_add]
            ring
          · exact ⟨et, het, hT⟩

/-! ## The pivot table's invariants, for the cancellations it performs -/

/-- `Q` is closed under the cancellations the pivot table performs: of a target by a reducer of no
larger shifted degree. -/
def CancelClosed (Q : PolynomialRow F → Prop) : Prop :=
  ∀ (target reducer : PolynomialRow F) (shift : Array Nat), Q target → Q reducer →
    (∀ t r, rowShiftedLeadingTerm? target shift = some t →
      rowShiftedLeadingTerm? reducer shift = some r → r.shiftedDegree ≤ t.shiftedDegree) →
    Q (cancelKernelLeafLeadingTerm target reducer shift)

theorem homRowLe_cancelClosed (B : Nat) : CancelClosed (F := F) (HomRowLe B) :=
  fun _ _ _ ht hr hle ↦ homRowLe_cancel ht hr hle

omit [BEq F] [LawfulBEq F] in
private theorem setIfInBounds_invariant (Q : PolynomialRow F → Prop)
    {pivots : Array (Option (PolynomialRow F))}
    (hpivots : ∀ p r, pivots.getD p none = some r → Q r)
    (position : Nat) (newRow : PolynomialRow F) (hnew : Q newRow) :
    ∀ p' r', (pivots.setIfInBounds position (some newRow)).getD p' none = some r' → Q r' := by
  intro p' r' hget'
  rw [array_getD_setIfInBounds] at hget'
  split_ifs at hget' with h
  · cases hget'
    exact hnew
  · exact hpivots p' r' hget'

/-- Pivot-table insertion keeps a predicate closed under the table's cancellations (CompPoly's
`insertKernelLeafPivotRowWithFuel_invariant`, for `CancelClosed`). -/
theorem insertPivot_invariant (Q : PolynomialRow F → Prop) (hclosed : CancelClosed Q) :
    ∀ (fuel : Nat) (pivots : Array (Option (PolynomialRow F)))
      (shift : Array Nat) (row : PolynomialRow F),
      (∀ p r, pivots.getD p none = some r → Q r) → Q row →
      ∀ p r,
        (insertKernelLeafPivotRowWithFuel fuel pivots shift row).getD p none =
          some r → Q r := by
  intro fuel
  induction fuel with
  | zero =>
      intro pivots shift row hpivots _hrow p r hget
      exact hpivots p r hget
  | succ fuel ih =>
      intro pivots shift row hpivots hrow p r hget
      rw [insertKernelLeafPivotRowWithFuel] at hget
      cases hterm : rowShiftedLeadingTerm? row shift with
      | none =>
          simp only [hterm] at hget
          exact hpivots p r hget
      | some target =>
          simp only [hterm] at hget
          cases hpivot : pivots.getD target.position none with
          | none =>
              simp only [hpivot] at hget
              exact setIfInBounds_invariant Q hpivots target.position row hrow p r hget
          | some pivot =>
              simp only [hpivot] at hget
              cases hpterm : rowShiftedLeadingTerm? pivot shift with
              | none =>
                  simp only [hpterm] at hget
                  exact setIfInBounds_invariant Q hpivots target.position row hrow p r hget
              | some reducer =>
                  simp only [hpterm] at hget
                  have hpivotrow : Q pivot := hpivots target.position pivot hpivot
                  split at hget
                  · rename_i hlt
                    refine ih (pivots.setIfInBounds target.position (some row)) shift
                      (cancelKernelLeafLeadingTerm pivot row shift)
                      (setIfInBounds_invariant Q hpivots target.position row hrow)
                      (hclosed _ _ _ hpivotrow hrow ?_) p r hget
                    intro t' r' h1 h2
                    rw [hpterm] at h1
                    rw [hterm] at h2
                    cases h1
                    cases h2
                    omega
                  · rename_i hlt
                    refine ih pivots shift (cancelKernelLeafLeadingTerm row pivot shift) hpivots
                      (hclosed _ _ _ hrow hpivotrow ?_) p r hget
                    intro t' r' h1 h2
                    rw [hterm] at h1
                    rw [hpterm] at h2
                    cases h1
                    cases h2
                    omega

/-- The pivot reduction keeps a `CancelClosed` predicate. -/
theorem reduceKernelLeafRowsByPivots_invariant' (Q : PolynomialRow F → Prop)
    (hclosed : CancelClosed Q) {rows : PolynomialMatrix F} (shift : Array Nat)
    (hrows : ∀ row ∈ MatrixRows rows, Q row) {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (reduceKernelLeafRowsByPivots rows shift)) : Q row := by
  rw [reduceKernelLeafRowsByPivots] at hrow
  refine pivotRows_invariant Q ?_ hrow
  have hfold : ∀ (l : List (PolynomialRow F)) (pivots : Array (Option (PolynomialRow F))),
      (∀ r ∈ l, Q r) → (∀ p r, pivots.getD p none = some r → Q r) →
      ∀ p r, (l.foldl (fun pivots row ↦
            insertKernelLeafPivotRowWithFuel (reduceKernelLeafFuel rows shift)
              pivots shift row) pivots).getD p none = some r → Q r := by
    intro l
    induction l with
    | nil =>
        intro pivots _hl hpivots p r hget
        exact hpivots p r hget
    | cons head tail ih =>
        intro pivots hl hpivots p r hget
        rw [List.foldl_cons] at hget
        refine ih _ (fun r hr ↦ hl r (List.mem_cons_of_mem head hr)) ?_ p r hget
        exact insertPivot_invariant Q hclosed _ pivots shift head hpivots
          (hl head List.mem_cons_self)
  rw [← Array.foldl_toList]
  refine hfold rows.toList _ (fun r hr ↦ hrows r hr) ?_
  intro p r hget
  rcases Nat.lt_or_ge p (Array.replicate (MatrixWidth rows)
      (none : Option (PolynomialRow F))).size with hp | hp
  · rw [array_getD_of_lt' _ _ hp, Array.getElem_replicate] at hget
    cases hget
  · rw [array_getD_of_le' _ _ hp] at hget
    cases hget

/-- The incremental pivot reduction keeps a `CancelClosed` predicate. -/
theorem reduceKernelLeafRowsIncremental_invariant' (Q : PolynomialRow F → Prop)
    (hclosed : CancelClosed Q) {rows : PolynomialMatrix F} (shift : Array Nat)
    (hrows : ∀ row ∈ MatrixRows rows, Q row) {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (reduceKernelLeafRowsIncremental rows shift)) : Q row := by
  rw [reduceKernelLeafRowsIncremental, ← Array.foldl_toList] at hrow
  have hfold : ∀ (l : List (PolynomialRow F)) (basis : PolynomialMatrix F),
      (∀ r ∈ l, Q r) → (∀ r ∈ MatrixRows basis, Q r) →
      ∀ r ∈ MatrixRows (l.foldl
        (fun basis row ↦ insertKernelLeafRowIncremental basis shift row) basis), Q r := by
    intro l
    induction l with
    | nil =>
        intro basis _hl hbasis r hr
        exact hbasis r hr
    | cons head tail ih =>
        intro basis hl hbasis r hr
        rw [List.foldl_cons] at hr
        refine ih _ (fun x hx ↦ hl x (List.mem_cons_of_mem head hx)) ?_ r hr
        intro x hx
        rw [insertKernelLeafRowIncremental] at hx
        have hx' : x ∈ MatrixRows (reduceKernelLeafRows (basis.push head) shift) := by
          rw [MatrixRows] at hx ⊢
          have hmem : x ∈ reduceKernelLeafRows (basis.push head) shift ∧
              rowIsZero x = false := by
            simpa using hx
          simpa using hmem.1
        rw [reduceKernelLeafRows] at hx'
        refine reduceKernelLeafRowsByPivots_invariant' Q hclosed shift ?_ hx'
        intro y hy
        rcases mem_matrixRows_push hy with hy | rfl
        · exact hbasis y hy
        · exact hl _ List.mem_cons_self
  exact hfold rows.toList #[] (fun r hr ↦ hrows r hr)
    (by intro r hr; simp [MatrixRows] at hr) row hrow

/-! ## The leaf at order one -/

omit [BEq F] [LawfulBEq F] in
theorem leafDegreeCap_eq_one {problem : XAdicProblem F} (h : maxOrder problem ≤ 1) :
    leafDegreeCap problem = 1 := by
  rw [leafDegreeCap]
  omega

/-- A kernel vector read back at cap one is a constant row. -/
theorem homRow_vectorToPolynomialRow (width : Nat) (v : Array F) :
    HomRow 0 (vectorToPolynomialRow 1 width v) := by
  intro j
  refine ⟨_, toPoly_eq_C_mul_X_pow_of_coeff (e := 0) fun k hk ↦ ?_⟩
  rw [rowGet_vectorToPolynomialRow_coeff, ite_eq_right (by omega)]

/-- `X^d·eᵢ` is homogeneous of degree `d`. -/
theorem homRow_monomialUnitRow (n i d : Nat) : HomRow d (monomialUnitRow (F := F) n i d) := by
  intro j
  rw [pm_rowGet_monomialUnitRow]
  split_ifs
  · exact ⟨1, coeffXPower_toPoly 1 d⟩
  · exact ⟨0, by rw [CPolynomial.toPoly_zero, map_zero, zero_mul]⟩

/-- **The leaf at order one returns homogeneous rows of degree at most one.** -/
theorem kernelLeafBasis_homRowLe_one (problem : XAdicProblem F) (shift : Array Nat)
    (h : maxOrder problem ≤ 1) :
    ∀ row ∈ MatrixRows (kernelLeafBasis problem shift), HomRowLe 1 row := by
  have hcap := leafDegreeCap_eq_one h
  intro row hrow
  simp only [kernelLeafBasis] at hrow
  rw [MatrixRows, completeMissingPivotRows, Array.toList_append] at hrow
  rcases List.mem_append.mp hrow with hmem | hmem
  · refine reduceKernelLeafRowsIncremental_invariant' _ (homRowLe_cancelClosed 1) shift ?_ hmem
    intro r hr
    rw [MatrixRows, Array.toList_append] at hr
    rcases List.mem_append.mp hr with hr | hr
    · rw [Array.toList_map] at hr
      rcases List.mem_map.mp hr with ⟨w, _hw, rfl⟩
      rw [hcap]
      exact ⟨0, Nat.zero_le 1, homRow_vectorToPolynomialRow _ w⟩
    · simp only [kernelLeafCompletionRows] at hr
      rcases List.mem_map.mp hr with ⟨i, _hi, rfl⟩
      rw [hcap]
      exact ⟨1, le_rfl, homRow_monomialUnitRow _ _ _⟩
  · rw [missingCompletionRows, List.toList_toArray] at hmem
    rcases List.mem_filterMap.mp hmem with ⟨i, _hi, hsome⟩
    split at hsome
    · cases hsome
    · cases hsome
      rw [hcap]
      exact ⟨1, le_rfl, homRow_monomialUnitRow _ _ _⟩

/-- **The leaf at order one has entries of degree at most one.** -/
theorem kernelLeafBasis_natDegree_le_one (problem : XAdicProblem F) (shift : Array Nat)
    (h : maxOrder problem ≤ 1) :
    ∀ row ∈ MatrixRows (kernelLeafBasis problem shift), ∀ j, (rowGet row j).natDegree ≤ 1 :=
  fun row hrow j ↦ (kernelLeafBasis_homRowLe_one problem shift h row hrow).natDegree_le j

/-! ## The leaf's shape at any cap: `r` rows with distinct leading positions -/

/-- Rows of width `n`, each with a shifted leading position (so nonzero), the positions pairwise
distinct. -/
def PivotShape (n : Nat) (shift : Array Nat) (rows : PolynomialMatrix F) : Prop :=
  (∀ r ∈ rows.toList, r.size = n ∧ (rowShiftedLeadingPosition? r shift).isSome) ∧
    (rows.toList.map fun r ↦ rowShiftedLeadingPosition? r shift).Nodup

omit [LawfulBEq F] in
/-- A pivot table whose slots hold rows of width `n` leading at the slot extracts to a
`PivotShape`. -/
theorem pivotShape_pivotRows {n : Nat} {shift : Array Nat}
    {pivots : Array (Option (PolynomialRow F))}
    (hinv : ∀ p r, pivots.getD p none = some r →
      r.size = n ∧ rowShiftedLeadingPosition? r shift = some p) :
    PivotShape n shift (pivotRows pivots) := by
  refine ⟨fun r hr ↦ pivotRows_invariant
    (fun r ↦ r.size = n ∧ (rowShiftedLeadingPosition? r shift).isSome)
    (fun p r hget ↦ ⟨(hinv p r hget).1, by rw [(hinv p r hget).2]; rfl⟩) hr, ?_⟩
  rw [pivotRows, List.toList_toArray, List.map_filterMap, List.Nodup, List.pairwise_filterMap,
    List.pairwise_iff_getElem]
  intro u v hu hv huv b hb b' hb'
  have hu' : u < pivots.size := by simpa using hu
  have hv' : v < pivots.size := by simpa using hv
  cases hpu : pivots.toList[u] with
  | none => rw [hpu] at hb; cases hb
  | some ru =>
      cases hpv : pivots.toList[v] with
      | none => rw [hpv] at hb'; cases hb'
      | some rv =>
          have hgu : pivots.getD u none = some ru := by
            rw [array_getD_of_lt' _ _ hu', ← Array.getElem_toList]; exact hpu
          have hgv : pivots.getD v none = some rv := by
            rw [array_getD_of_lt' _ _ hv', ← Array.getElem_toList]; exact hpv
          rw [hpu] at hb
          rw [hpv] at hb'
          simp only [id, Option.map_some, Option.some.injEq] at hb hb'
          rw [← hb, ← hb', (hinv u ru hgu).2, (hinv v rv hgv).2]
          intro h
          cases h
          omega

omit [LawfulBEq F] in
theorem PivotShape.filter {n : Nat} {shift : Array Nat} {rows : PolynomialMatrix F}
    (h : PivotShape n shift rows) (f : PolynomialRow F → Bool) :
    PivotShape n shift (rows.filter f) := by
  rw [PivotShape, Array.toList_filter]
  exact ⟨fun r hr ↦ h.1 r (List.mem_filter.mp hr).1,
    h.2.sublist ((List.filter_sublist).map _)⟩

theorem PivotShape.rowIsZero_eq_false {n : Nat} {shift : Array Nat} {rows : PolynomialMatrix F}
    (h : PivotShape n shift rows) {r : PolynomialRow F} (hr : r ∈ rows.toList) :
    rowIsZero r = false := by
  have hpos := (h.1 r hr).2
  cases hb : rowIsZero r
  · rfl
  · have hz := (rowShiftedDegree?_eq_none_iff (shift := shift)).2 (rowIsZero_iff.1 hb)
    rw [rowShiftedLeadingPosition?, hz] at hpos
    cases hpos

theorem PivotShape.compactNonzeroRows_eq {n : Nat} {shift : Array Nat}
    {rows : PolynomialMatrix F} (h : PivotShape n shift rows) :
    compactNonzeroRows rows = rows := by
  rw [compactNonzeroRows, Array.filter_eq_self]
  intro r hr
  rw [h.rowIsZero_eq_false (Array.mem_toList_iff.mpr hr)]
  rfl

omit [LawfulBEq F] in
theorem PivotShape.shiftedWeakPopov {n : Nat} {shift : Array Nat} {rows : PolynomialMatrix F}
    (h : PivotShape n shift rows) : ShiftedWeakPopov rows shift := by
  intro i j hi hj hij _ _
  have hnd := h.2
  rw [List.Nodup, List.pairwise_iff_getElem] at hnd
  rw [array_getD_of_lt' _ _ hi, array_getD_of_lt' _ _ hj]
  rcases Nat.lt_or_gt_of_ne hij with h' | h'
  · have h2 := hnd i j (by simpa using hi) (by simpa using hj) h'
    rw [List.getElem_map, List.getElem_map, Array.getElem_toList, Array.getElem_toList] at h2
    exact h2
  · have h2 := hnd j i (by simpa using hj) (by simpa using hi) h'
    rw [List.getElem_map, List.getElem_map, Array.getElem_toList, Array.getElem_toList] at h2
    exact Ne.symm h2

/-- The incremental pivot reduction of rows of width `n` has the `PivotShape`. -/
theorem pivotShape_reduceKernelLeafRowsIncremental {n : Nat} {rows : PolynomialMatrix F}
    (shift : Array Nat) (hrows : ∀ r ∈ rows.toList, r.size = n) :
    PivotShape n shift (reduceKernelLeafRowsIncremental rows shift) := by
  rw [reduceKernelLeafRowsIncremental, ← Array.foldl_toList]
  have hfold : ∀ (l : List (PolynomialRow F)) (basis : PolynomialMatrix F),
      (∀ r ∈ l, r.size = n) → PivotShape n shift basis →
      PivotShape n shift (l.foldl
        (fun basis row ↦ insertKernelLeafRowIncremental basis shift row) basis) := by
    intro l
    induction l with
    | nil => intro basis _ hb; exact hb
    | cons head tail ih =>
        intro basis hl hb
        rw [List.foldl_cons]
        refine ih _ (fun r hr ↦ hl r (List.mem_cons_of_mem head hr)) ?_
        rw [insertKernelLeafRowIncremental, reduceKernelLeafRows, reduceKernelLeafRowsByPivots,
          ← Array.foldl_toList]
        refine PivotShape.filter (pivotShape_pivotRows ?_) _
        refine insertKernelLeaf_foldl_pivotInv (n := n) _ _ _ shift ?_ ?_
        · intro r hr
          rw [Array.toList_push, List.mem_append] at hr
          rcases hr with hr | hr
          · exact (hb.1 r hr).1
          · rw [List.mem_singleton] at hr
            rw [hr]
            exact hl head List.mem_cons_self
        · intro p r hget
          rcases Nat.lt_or_ge p (Array.replicate (MatrixWidth (basis.push head))
              (none : Option (PolynomialRow F))).size with hp | hp
          · rw [array_getD_of_lt' _ _ hp, Array.getElem_replicate] at hget
            cases hget
          · rw [array_getD_of_le' _ _ hp] at hget
            cases hget
  exact hfold rows.toList #[] hrows ⟨by simp, by simp⟩

/-- `X^cap·eᵢ` leads at `i`. -/
theorem rowShiftedLeadingPosition_monomialUnitRow {n i : Nat} (cap : Nat) (shift : Array Nat)
    (hi : i < n) :
    rowShiftedLeadingPosition? (monomialUnitRow (F := F) n i cap) shift = some i := by
  have hget := pm_rowGet_monomialUnitRow (F := F) n i cap
  have hne : coeffXPower (1 : F) cap ≠ 0 := by
    intro h
    have h' := congrArg CPolynomial.toPoly h
    rw [coeffXPower_toPoly, CPolynomial.toPoly_zero, map_one, one_mul] at h'
    exact pow_ne_zero _ Polynomial.X_ne_zero h'
  have hsize : (monomialUnitRow (F := F) n i cap).size = n := by simp [monomialUnitRow]
  have hii : rowGet (monomialUnitRow (F := F) n i cap) i ≠ 0 := by
    rw [hget, ite_eq_left ⟨hi, rfl⟩]
    exact hne
  have hoff : ∀ j, j ≠ i → shiftedEntryDegree? (monomialUnitRow (F := F) n i cap) shift j =
      none := by
    intro j hj
    have hz : rowGet (monomialUnitRow (F := F) n i cap) j = 0 := by
      rw [hget, ite_eq_right (fun h ↦ hj h.2.symm)]
    simp [shiftedEntryDegree?, hz]
  cases hD : rowShiftedDegree? (monomialUnitRow (F := F) n i cap) shift with
  | none =>
      exfalso
      apply hii
      have hz := rowShiftedDegree?_eq_none_iff.1 hD
      rw [rowGet, array_getD_of_lt' _ _ (by rw [hsize]; exact hi)]
      exact hz _ (Array.getElem_mem_toList _)
  | some D =>
      obtain ⟨pos, hpos⟩ := rowShiftedLeadingPosition?_some_of_degree hD
      have hentry := rowShiftedLeadingPosition?_entry_eq hD hpos
      by_cases h : pos = i
      · rw [hpos, h]
      · rw [hoff pos h] at hentry
        cases hentry

omit [LawfulBEq F] in
theorem rowsContainLeadingPosition_iff {rows : PolynomialMatrix F} {shift : Array Nat}
    {i : Nat} :
    rowsContainLeadingPosition rows shift i = true ↔
      some i ∈ rows.toList.map fun r ↦ rowShiftedLeadingPosition? r shift := by
  rw [rowsContainLeadingPosition, Array.any_eq_true', List.mem_map]
  constructor
  · rintro ⟨r, hr, hp⟩
    refine ⟨r, Array.mem_toList_iff.mpr hr, ?_⟩
    split at hp
    · rename_i p hpos
      rw [hpos, beq_iff_eq.mp hp]
    · cases hp
  · rintro ⟨r, hr, hp⟩
    refine ⟨r, Array.mem_toList_iff.mp hr, ?_⟩
    rw [hp]
    exact beq_self_eq_true i

private theorem filterMap_ite_eq {α β : Type*} (c : α → Bool) (g : α → β) (l : List α) :
    l.filterMap (fun i ↦ if c i then none else some (g i)) =
      (l.filter fun i ↦ !c i).map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases hc : c a <;> simp [hc, ih]

/-- **Completion of a `PivotShape` gives exactly `r` rows, in `PivotShape`.** -/
theorem completeMissingPivotRows_shape (problem : XAdicProblem F) (shift : Array Nat)
    {red : PolynomialMatrix F} (hred : PivotShape problem.matrix.size shift red) :
    (completeMissingPivotRows problem shift red).size = problem.matrix.size ∧
      PivotShape problem.matrix.size shift (completeMissingPivotRows problem shift red) := by
  set m := problem.matrix.size with hm
  set pos : PolynomialRow F → Option Nat := fun r ↦ rowShiftedLeadingPosition? r shift
    with hposdef
  set c : Nat → Bool := fun i ↦ rowsContainLeadingPosition red shift i with hcdef
  have hmiss : (missingCompletionRows problem shift red).toList =
      ((List.range m).filter fun i ↦ !c i).map
        fun i ↦ monomialUnitRow m i (leafDegreeCap problem) := by
    rw [missingCompletionRows, List.toList_toArray]
    exact filterMap_ite_eq _ _ _
  have hc : ∀ i, c i = true ↔ some i ∈ red.toList.map pos := fun i ↦
    rowsContainLeadingPosition_iff
  -- every position of `red` is `some p` with `p < m`
  have hredpos : ∀ x ∈ red.toList.map pos, ∃ p, p < m ∧ x = some p := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
    obtain ⟨hsz, hsome⟩ := hred.1 r hr
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨p, hsz ▸ rowShiftedLeadingPosition?_lt hp, hp⟩
  have hmisspos : (((List.range m).filter fun i ↦ !c i).map
      fun i ↦ monomialUnitRow (F := F) m i (leafDegreeCap problem)).map pos =
      ((List.range m).filter fun i ↦ !c i).map some := by
    rw [List.map_map]
    refine List.map_congr_left fun i hi ↦ ?_
    have him : i < m := List.mem_range.mp (List.mem_filter.mp hi).1
    exact rowShiftedLeadingPosition_monomialUnitRow _ shift him
  have hperm : List.Perm (((List.range m).filter c).map some) (red.toList.map pos) := by
    refine (List.perm_ext_iff_of_nodup ((List.nodup_range.filter _).map
      fun _ _ h ↦ Option.some.inj h) hred.2).mpr fun x ↦ ?_
    constructor
    · intro hx
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      exact (hc i).mp (List.mem_filter.mp hi).2
    · intro hx
      obtain ⟨p, hp, rfl⟩ := hredpos x hx
      exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨List.mem_range.mpr hp, (hc p).mpr hx⟩,
        rfl⟩
  constructor
  · rw [completeMissingPivotRows, Array.size_append, ← Array.length_toList (xs :=
      missingCompletionRows problem shift red), hmiss, List.length_map]
    have hsplit : m = ((List.range m).filter c).length +
        ((List.range m).filter fun i ↦ !c i).length := by
      have h := List.length_eq_length_filter_add (l := List.range m) c
      rwa [List.length_range] at h
    have hlen : ((List.range m).filter c).length = red.size := by
      have h := hperm.length_eq
      simpa only [List.length_map, Array.length_toList] using h
    omega
  · rw [PivotShape, completeMissingPivotRows, Array.toList_append, hmiss]
    constructor
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hred.1 r hr
      · rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
        have him : i < m := List.mem_range.mp (List.mem_filter.mp hi).1
        refine ⟨by simp [monomialUnitRow], ?_⟩
        rw [rowShiftedLeadingPosition_monomialUnitRow _ shift him]
        rfl
    · rw [List.map_append, hmisspos, List.nodup_append]
      refine ⟨hred.2, (List.nodup_range.filter _).map fun _ _ h ↦ Option.some.inj h, ?_⟩
      intro a ha b hb hab
      rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
      have hci := (List.mem_filter.mp hi).2
      rw [(hc i).mpr (hab ▸ ha)] at hci
      cases hci

/-- **The leaf has exactly `r` rows**, of width `r`, nonzero, with pairwise distinct shifted
leading positions (at any cap). -/
theorem kernelLeafBasis_shape (problem : XAdicProblem F) (shift : Array Nat) :
    (kernelLeafBasis problem shift).size = problem.matrix.size ∧
      PivotShape problem.matrix.size shift (kernelLeafBasis problem shift) := by
  simp only [kernelLeafBasis]
  refine completeMissingPivotRows_shape problem shift
    (pivotShape_reduceKernelLeafRowsIncremental shift ?_)
  intro r hr
  rw [Array.toList_append] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [Array.toList_map] at hr
    rcases List.mem_map.mp hr with ⟨w, _hw, rfl⟩
    simp [vectorToPolynomialRow]
  · simp only [kernelLeafCompletionRows, List.toList_toArray] at hr
    rcases List.mem_map.mp hr with ⟨i, _hi, rfl⟩
    simp [monomialUnitRow]

/-- **The PM-basis leaf at order one** (`maxOrder problem ≤ 1`, any matrix, any shift): exactly
`r = problem.matrix.size` rows, each of width `r` and nonzero (so the recursion's
`compactNonzeroRows` keeps them all), shifted weak Popov, every row `X^e·v` with `v` constant and
`e ≤ 1`, so every entry of degree at most one. -/
theorem kernelLeafBasis_orderOne (problem : XAdicProblem F) (shift : Array Nat)
    (h : maxOrder problem ≤ 1) :
    (kernelLeafBasis problem shift).size = problem.matrix.size ∧
      compactNonzeroRows (kernelLeafBasis problem shift) = kernelLeafBasis problem shift ∧
      ShiftedWeakPopov (kernelLeafBasis problem shift) shift ∧
      ∀ row ∈ MatrixRows (kernelLeafBasis problem shift),
        row.size = problem.matrix.size ∧ rowIsZero row = false ∧ HomRowLe 1 row ∧
          ∀ j, (rowGet row j).natDegree ≤ 1 := by
  obtain ⟨hsize, hshape⟩ := kernelLeafBasis_shape problem shift
  refine ⟨hsize, hshape.compactNonzeroRows_eq, hshape.shiftedWeakPopov, fun row hrow ↦
    ⟨(hshape.1 row hrow).1, hshape.rowIsZero_eq_false hrow,
      kernelLeafBasis_homRowLe_one problem shift h row hrow,
      kernelLeafBasis_natDegree_le_one problem shift h row hrow⟩⟩

end

end LeanVM.Extraction.Fast.PMDegree
