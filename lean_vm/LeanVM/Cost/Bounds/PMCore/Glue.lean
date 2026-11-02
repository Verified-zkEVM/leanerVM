module

public import LeanVM.Cost.Extractor.PMCore
public import LeanVM.Cost.Bounds.Decoder.MsStep
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf
import all CompPoly.LinearAlgebra.PolynomialMatrix.Degree
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic

/-!
# Bounds: the PM-basis node's glue, compiled

The compiled helpers of the PM-basis recursion (`Cost/Extractor/PMCore.lean`) besides its two
matrix products and its leaf, each for every program holding its bodies:

* `maxOrderC_cost` (`18·|orders| + 9`), `lowerOrdersC_cost` (`21·|orders| + 11`),
  `residualOrdersC_cost` (`19·|orders| + 11`): the folds and maps over the orders;
* `divXTruncC_cost` (`59·order + 36`): one residual entry;
* `updateShiftByRowsC_cost` (`(90·C + 71)·R + 20`): the shift update, `R` rows of at most `C`
  entries (`rowShiftedDegree_cost`: a constant per entry);
* `compactNonzeroRowsC_cost` (`((3·D + 23)·C + 28)·R + 8`): the zero-row filter, `R` rows of at
  most `C` entries of at most `D` coefficients (the zero test reads an entry's coefficients);
* `ofFnC_cost` (`R·((E + 33)·W + 66) + 19`): `PolynomialMatrix.ofFn`, an entry at most `E`.

Word-sized orders, shifts, sizes throughout.
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Cost.Bounds.Decoder CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

variable (P : MachineProgram)

/-! ## The orders -/

/-- **`maxOrder`** (`maxOrderC`): at most `18·|orders| + 9`, word-sized orders. -/
theorem maxOrderC_cost (hP : Includes P maxOrderC.costDeps) (problem : XAdicProblem K)
    (h : ∀ x ∈ problem.orders, x < 2 ^ 63) :
    machineCost P maxOrderC.costIdx [encodeValue problem] ≤ 18 * problem.orders.size + 9 := by
  rw [maxOrderC.costEq P hP]
  have hf := listFoldl_le P (by includes) (fun a b : ℕ ↦ max a b) (.closure maxOrderC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (maxOrderC.lam0.costSpec P (by includes) a b)) 6
    (fun acc ↦ acc < 2 ^ 63) problem.orders.toList 0 (by norm_num)
    (fun acc hacc b hb ↦ ⟨by have := h b (by simpa using hb); omega, by
      rw [appCost_fn, List.nil_append, maxOrderC.lam0.costEq P (by includes),
        limbs_of_lt (by omega : acc < 2 ^ 64),
        limbs_of_lt (by have := h b (by simpa using hb); omega : b < 2 ^ 64)]
      split_ifs <;> omega⟩)
  simp only [Array.length_toList] at hf
  omega

/-- **`lowerOrders`** (`lowerOrdersC`): at most `21·|orders| + 11`. -/
theorem lowerOrdersC_cost (hP : Includes P lowerOrdersC.costDeps) (problem : XAdicProblem K)
    (d : ℕ) (hd : d < 2 ^ 64) (h : ∀ x ∈ problem.orders, x < 2 ^ 64) :
    machineCost P lowerOrdersC.costIdx [encodeValue problem, encodeValue d] ≤
      21 * problem.orders.size + 11 := by
  rw [lowerOrdersC.costEq P hP]
  have hm := map_cost P (by includes) (fun order : ℕ ↦ min order d)
    (.closure lowerOrdersC.lam0.costIdx [encodeValue d])
    (fun a ↦ RunsApp.of_spec (lowerOrdersC.lam0.costSpec P (by includes) d a)) 6
    problem.orders.toList (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append, lowerOrdersC.lam0.costEq P (by includes),
        limbs_of_lt (h a (by simpa using ha)), limbs_of_lt hd]
      split_ifs <;> omega)
  simp only [Array.length_toList, List.length_map] at hm ⊢
  omega

/-- **`residualOrders`** (`residualOrdersC`): at most `19·|orders| + 11`. -/
theorem residualOrdersC_cost (hP : Includes P residualOrdersC.costDeps) (problem : XAdicProblem K)
    (d : ℕ) (hd : d < 2 ^ 64) (h : ∀ x ∈ problem.orders, x < 2 ^ 64) :
    machineCost P residualOrdersC.costIdx [encodeValue problem, encodeValue d] ≤
      19 * problem.orders.size + 11 := by
  rw [residualOrdersC.costEq P hP]
  have hm := map_cost P (by includes) (fun order : ℕ ↦ order - d)
    (.closure residualOrdersC.lam0.costIdx [encodeValue d])
    (fun a ↦ RunsApp.of_spec (residualOrdersC.lam0.costSpec P (by includes) d a)) 4
    problem.orders.toList (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append, residualOrdersC.lam0.costEq P (by includes),
        limbs_of_lt (h a (by simpa using ha)), limbs_of_lt hd]
      simp)
  simp only [Array.length_toList, List.length_map] at hm ⊢
  omega

/-! ## One residual entry -/

/-- **`divXTrunc shift order p`** (`divXTruncC`): at most `59·order + 36`. -/
theorem divXTruncC_cost (hP : Includes P divXTruncC.costDeps) (shift order : ℕ)
    (p : CPolynomial K) (h : shift + order < 2 ^ 63) :
    machineCost P divXTruncC.costIdx [encodeValue shift, encodeValue order, encodeValue p] ≤
      59 * order + 36 := by
  rw [divXTruncC.costEq P hP]
  have hr := rangeLoop_cost P (by includes) order [] (by omega)
  have hm := map_cost P (by includes) (fun i ↦ p.coeff (i + shift))
    (.closure divXTruncC.lam0.costIdx [encodeValue shift, encodeValue p])
    (fun a ↦ RunsApp.of_spec (divXTruncC.lam0.costSpec P (by includes) shift p a)) 7
    (List.range order) (fun a ha ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        divXTruncC.lam0.costEq P (by includes),
        limbs_of_lt (by have := List.mem_range.1 ha; omega : a < 2 ^ 64),
        limbs_of_lt (by omega : shift < 2 ^ 64)]
      simp)
  have ho := ofArray_cost P (by includes)
    (List.map (fun i ↦ p.coeff (i + shift)) (List.range order)).toArray (by simp; omega)
  simp only [List.length_range, List.length_map, List.size_toArray] at hm ho ⊢
  omega

/-! ## The shift update and the zero-row filter -/

/-- **`updateShiftByRows`** (`updateShiftByRowsC`): `R` rows of at most `C` entries of at most
`D` coefficients, shifts at most `S`: at most `(90·C + 71)·R + 20`. -/
theorem updateShiftByRowsC_cost (hP : Includes P updateShiftByRowsC.costDeps)
    {C D S : ℕ} (hC : C < 2 ^ 62) (hDS : D + S < 2 ^ 62) (basis : PolynomialMatrix K)
    (hR : basis.size < 2 ^ 62) (hrows : ∀ i, RowWithin C D (basis.getD i #[]))
    (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P updateShiftByRowsC.costIdx [encodeValue basis, encodeValue shift] ≤
      (90 * C + 71) * basis.size + 20 := by
  rw [updateShiftByRowsC.costEq P hP]
  have hr := rangeLoop_cost P (by includes) basis.size [] (by omega)
  have hm := map_cost P (by includes) _
    (.closure updateShiftByRowsC.lam0.costIdx [encodeValue basis, encodeValue shift])
    (fun a ↦ RunsApp.of_spec (updateShiftByRowsC.lam0.costSpec P (by includes) basis shift a))
    (90 * C + 42) (List.range basis.size) (fun a _ ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        updateShiftByRowsC.lam0.costEq P (by includes)]
      have := rowShiftedDegree_cost P (by includes) hC hDS (basis.getD a #[]) (hrows a) shift hS
      cases rowShiftedDegree? (basis.getD a #[]) shift <;> dsimp only <;> omega)
  simp only [List.length_range, List.length_map] at hm ⊢
  nlinarith

/-- The zero test of one entry: at most `3·|p| + 11`. -/
theorem rowIsZeroLam_cost (hP : Includes P Auto.CompPoly.PolynomialMatrix.rowIsZero.c955.lam0.costDeps)
    (p : CPolynomial K) :
    machineCost P Auto.CompPoly.PolynomialMatrix.rowIsZero.c955.lam0.costIdx [encodeValue p] ≤
      3 * p.val.size + 11 := by
  rw [Auto.CompPoly.PolynomialMatrix.rowIsZero.c955.lam0.costEq P hP]
  have h0 : (0 : CPolynomial K).val.size = 0 := rfl
  have hl : (0 : CPolynomial K).val.toList = [] := rfl
  rw [h0, hl]
  cases hq : p.val.toList with
  | nil => rw [Auto.List.beq.c27.costEq_nil P (by includes)]; simp
  | cons x l => rw [Auto.List.beq.c27.costEq_cons P (by includes)]; simp

/-- **`rowIsZero`**: a row of at most `C` entries of at most `D` coefficients, at most
`(3·D + 23)·C + 7`. -/
theorem rowIsZeroC_cost (hP : Includes P Auto.CompPoly.PolynomialMatrix.rowIsZero.c955.costDeps)
    {C D : ℕ} (row : PolynomialRow K) (h : RowWithin C D row) :
    machineCost P Auto.CompPoly.PolynomialMatrix.rowIsZero.c955.costIdx [encodeValue row] ≤
      (3 * D + 23) * C + 7 := by
  rw [Auto.CompPoly.PolynomialMatrix.rowIsZero.c955.costEq P hP]
  have ha := all_cost P (by includes) (fun p : CPolynomial K ↦ p == 0)
    (.closure Auto.CompPoly.PolynomialMatrix.rowIsZero.c955.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.rowIsZero.c955.lam0.costSpec P (by includes) a))
    (3 * D + 11) row.toList (fun a ha ↦ by
      rw [appCost_fn, List.nil_append]
      have := rowIsZeroLam_cost P (by includes) a
      have := h.2 a (by simpa using ha)
      omega)
  have hs := h.1
  simp only [Array.length_toList] at ha
  have : (3 * D + 11 + 9) * row.size ≤ (3 * D + 20) * C := Nat.mul_le_mul_left _ hs
  nlinarith

/-- **`compactNonzeroRows`** (`compactNonzeroRowsC`): `R` rows of at most `C` entries of at most
`D` coefficients, at most `((3·D + 23)·C + 28)·R + 8`. -/
theorem compactNonzeroRowsC_cost (hP : Includes P compactNonzeroRowsC.costDeps)
    {C D : ℕ} (rows : PolynomialMatrix K) (h : ∀ row ∈ rows.toList, RowWithin C D row) :
    machineCost P compactNonzeroRowsC.costIdx [encodeValue rows] ≤
      ((3 * D + 23) * C + 28) * rows.size + 8 := by
  rw [compactNonzeroRowsC.costEq P hP]
  have hf := filter_cost P (by includes) (fun row ↦ !rowIsZero row)
    (.closure compactNonzeroRowsC.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (compactNonzeroRowsC.lam0.costSpec P (by includes) a))
    ((3 * D + 23) * C + 11) rows.toList (fun a ha ↦ by
      rw [appCost_fn, List.nil_append, compactNonzeroRowsC.lam0.costEq P (by includes)]
      have := rowIsZeroC_cost P (by includes) a (h a ha)
      omega)
  have hl := List.length_filter_le (fun row ↦ !rowIsZero row) rows.toList
  simp only [Array.length_toList] at hf hl
  nlinarith

/-- The matrix's width (`MatrixWidth.c38`): at most `15`. -/
theorem matrixWidthC_cost (hP : Includes P Auto.CompPoly.PolynomialMatrix.MatrixWidth.c38.costDeps)
    (M : PolynomialMatrix K) (hMs : M.size < 2 ^ 64) :
    machineCost P Auto.CompPoly.PolynomialMatrix.MatrixWidth.c38.costIdx [encodeValue M] ≤ 15 := by
  rw [Auto.CompPoly.PolynomialMatrix.MatrixWidth.c38.costEq P hP]
  cost_simp
  cases M[0]? <;> dsimp only <;> split_ifs <;> omega

/-! ## `PolynomialMatrix.ofFn` -/

/-- **`PolynomialMatrix.ofFn rows width entry`** (`ofFn.c920`), each entry at most `E`: at most
`rows·((E + 33)·width + 66) + 19`. -/
theorem ofFnC_cost (hP : Includes P Auto.CompPoly.PolynomialMatrix.ofFn.c920.costDeps)
    (rows width : ℕ) (hrows : rows < 2 ^ 64) (hwidth : width < 2 ^ 64)
    (entry : ℕ → ℕ → CPolynomial K) (eVal : MachineValue)
    (he : ∀ a b, RunsApp P eVal [encodeValue a, encodeValue b] (encodeValue (entry a b))) (E : ℕ)
    (hE : ∀ i < rows, ∀ j < width, appCost P eVal [encodeValue i, encodeValue j] ≤ E) :
    machineCost P Auto.CompPoly.PolynomialMatrix.ofFn.c920.costIdx
        [encodeValue rows, encodeValue width, eVal] ≤
      rows * ((E + 33) * width + 66) + 19 := by
  rw [Auto.CompPoly.PolynomialMatrix.ofFn.c920.costEq P hP rows width entry eVal he]
  have hr := rangeLoop_cost P (by includes) rows [] hrows
  have hm := map_cost P (by includes)
    (fun i ↦ (List.map (fun j ↦ entry i j) (List.range width)).toArray)
    (.closure Auto.CompPoly.PolynomialMatrix.ofFn.c920.lam0.costIdx [encodeValue width, eVal])
    (fun a ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.ofFn.c920.lam0.costSpec P (by includes) width entry eVal he a))
    ((E + 33) * width + 37) (List.range rows) (fun i hi ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Auto.CompPoly.PolynomialMatrix.ofFn.c920.lam0.costEq P (by includes) width entry eVal he]
      have hr' := rangeLoop_cost P (by includes) width [] hwidth
      have hm' := map_cost P (by includes) (fun j ↦ entry i j)
        (.closure Auto.CompPoly.PolynomialMatrix.ofFn.c920.lam0.lam0.costIdx [eVal, encodeValue i])
        (fun a ↦ RunsApp.of_spec
          (Auto.CompPoly.PolynomialMatrix.ofFn.c920.lam0.lam0.costSpec P (by includes) entry eVal he i a))
        (E + 4) (List.range width) (fun j hj ↦ by
          rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
            Auto.CompPoly.PolynomialMatrix.ofFn.c920.lam0.lam0.costEq P (by includes) entry eVal he]
          have := hE i (List.mem_range.1 hi) j (List.mem_range.1 hj)
          omega)
      simp only [List.length_range, List.length_map] at hm' ⊢
      nlinarith)
  simp only [List.length_range, List.length_map] at hm ⊢
  nlinarith

end

end LeanVM.Cost.Bounds.PMCore
