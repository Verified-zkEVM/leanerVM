module

public import LeanVM.Cost.Bounds.Decoder.BivSizes
public import LeanVM.Cost.Extractor.PMLane
public import LeanVM.Cost.Bounds.Decoder.ShapeDefs
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic
import all CompPoly.Bivariate.CoeffRows
import all CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Algorithm
import all CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Basic

/-!
# Bound: the interpolation's normalization, compiled

The last step of a lane's interpolation (`interpolateDistinctWith pmSolver`, bounded in
`Bounds/PMSolve/Interp.lean`): the least row read as a bivariate polynomial (`ofCoeffRowC_cost`),
and its normalization (`normalizeLeeFastC_cost`): the first nonzero coefficient of the grid
(`leePivotC_cost`: at most `W + 1` coefficients tested per row) and every coefficient of the grid
divided by it (`leeScaledC_cost`: an inverse per coefficient, see the note below).

**Honest-cost note.** `leeScaled` divides every coefficient of the grid by the pivot: the compiled
division inverts the pivot again for each coefficient (`invItohTsujii`, `≤ 19700`, against `258`
for a product), a constant factor `≈ 76` on the normalization, `≈ 2^58` at `(28, 4)`.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open CompPoly.GuruswamiSudan CompPoly.PolynomialMatrix

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-! ## Library functions -/

theorem length_ofFnFrom {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) :
    (Rewrite.ofFnFrom f i).length = n - i := by
  rw [Rewrite.ofFnFrom_eq f (n - i) i rfl]
  simp

/-! ## The normalization -/

/-- `leeRows`: at most `15`. -/
theorem leeRowsC_cost (hP : Includes P leeRows.c635.costDeps) (params : GSInterpParams)
    (Q : CBivariate K) (hW : params.weightedDegreeBound + 1 < 2 ^ 64) (hQ : Q.val.size < 2 ^ 64) :
    machineCost P leeRows.c635.costIdx [encodeValue params, encodeValue Q] ≤ 15 := by
  rw [leeRows.c635.costEq P hP]
  cost_simp
  split_ifs <;> omega

/-- `leeCols` at row `y`: at most `50`. -/
theorem leeColsC_cost (hP : Includes P leeCols.c634.costDeps) (params : GSInterpParams)
    (Q : CBivariate K) (y : ℕ) (hW : params.weightedDegreeBound + 1 < 2 ^ 64)
    (hk : params.messageDegree < 2 ^ 64) (hy : y < 2 ^ 64) (hyw : yWeight params * y < 2 ^ 64)
    (hq : (Q.val.coeff y).val.size < 2 ^ 64) :
    machineCost P leeCols.c634.costIdx [encodeValue params, encodeValue Q, encodeValue y] ≤ 50 := by
  have hyw' : yWeight params < 2 ^ 64 := by unfold yWeight; omega
  rw [leeCols.c634.costEq P hP]
  cost_simp
  split_ifs <;> omega

theorem leeRows_le (params : GSInterpParams) (Q : CBivariate K) :
    leeRows params Q ≤ params.weightedDegreeBound + 1 ∧ leeRows params Q ≤ Q.val.size := by
  unfold leeRows; omega

theorem leeCols_le (params : GSInterpParams) (Q : CBivariate K) (y : ℕ) :
    leeCols params Q y ≤ params.weightedDegreeBound + 1 := by
  unfold leeCols; omega

theorem coeff_size_le_of_innerLe {Q : CBivariate K} {A : ℕ} (h : InnerLe Q.val A) (y : ℕ) :
    (Q.val.coeff y).val.size ≤ A := by
  rw [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?]
  cases hy : Q.val[y]? with
  | none => exact Nat.zero_le _
  | some e => exact h e (Array.mem_of_getElem? hy)

/-- The parameters' sizes the normalization reads. -/
@[expose] def NormSizes (params : GSInterpParams) (A : ℕ) : Prop :=
  params.weightedDegreeBound + 1 < 2 ^ 60 ∧ params.messageDegree < 2 ^ 64 ∧
    yWeight params * (params.weightedDegreeBound + 1) < 2 ^ 64 ∧ A < 2 ^ 64

/-- **The pivot** (`leePivot?`: rows scanned in order, each up to its first nonzero coefficient):
at most `(42·(W + 1) + 113)·rows + 35`, `rows = leeRows params Q`. -/
theorem leePivotC_cost (hP : Includes P leePivot?.c636.costDeps) (params : GSInterpParams)
    (Q : CBivariate K) {A : ℕ} (hs : NormSizes params A) (hQ : InnerLe Q.val A)
    (hQs : Q.val.size < 2 ^ 64) :
    machineCost P leePivot?.c636.costIdx [encodeValue params, encodeValue Q] ≤
      (42 * (params.weightedDegreeBound + 1) + 113) * leeRows params Q + 35 := by
  obtain ⟨hW, hk, hyW, hA⟩ := hs
  have hR := leeRows_le params Q
  rw [leePivot?.c636.costEq P hP]
  have := leeRowsC_cost P (by includes) params Q (by omega) hQs
  have := rangeLoop_cost P (by includes) (leeRows params Q) [] (by omega)
  have hf := fun y ↦ RunsApp.of_spec (us := [encodeValue params, encodeValue Q]) (vs := [encodeValue y])
    (leePivot?.c636.lam0.costSpec P (by includes) params Q y)
  have hfs := findSome_cost P (by includes) _ (.closure leePivot?.c636.lam0.costIdx [encodeValue params, encodeValue Q])
    hf (42 * (params.weightedDegreeBound + 1) + 87) (List.range (leeRows params Q)) (fun y hy ↦ by
      rw [List.mem_range] at hy
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [leePivot?.c636.lam0.costEq P (by includes)]
      have hyw : yWeight params * y < 2 ^ 64 := by
        have := Nat.mul_le_mul_left (yWeight params) (show y ≤ params.weightedDegreeBound + 1 by
          omega)
        omega
      have := leeColsC_cost P (by includes) params Q y (by omega) hk (by omega) hyw
        (by have := coeff_size_le_of_innerLe hQ y; omega)
      have hc := leeCols_le params Q y
      have := rangeLoop_cost P (by includes) (leeCols params Q y) [] (by omega)
      have hp := fun x ↦ RunsApp.of_spec (us := [encodeValue Q, encodeValue y]) (vs := [encodeValue x])
        (leePivot?.c636.lam0.lam1.costSpec P (by includes) Q y x)
      have := findNat_cost P (by includes) _ (.closure leePivot?.c636.lam0.lam1.costIdx [encodeValue Q, encodeValue y])
        hp 16 (List.range (leeCols params Q y)) (fun x _ ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append]
          rw [leePivot?.c636.lam0.lam1.costEq P (by includes),
            Auto.CompPoly.CBivariate.coeff.c633.costEq P (by includes)])
      have hm := fun x ↦ RunsApp.of_spec (us := [encodeValue y]) (vs := [encodeValue x])
        (leePivot?.c636.lam0.lam0.costSpec P (by includes) y x)
      have := optionMap_cost P (by includes)
        (fun x ↦ ({ xDegree := x, yDegree := y } : CBivariate.Monomial))
        (.closure leePivot?.c636.lam0.lam0.costIdx [encodeValue y]) hm
        5 ((List.range (leeCols params Q y)).find? fun x ↦ !Q.coeff x y == 0) (fun x _ ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append]
          rw [leePivot?.c636.lam0.lam0.costEq P (by includes)])
      simp only [List.length_range] at *
      omega)
  simp only [List.length_range] at hfs
  have e : (42 * (params.weightedDegreeBound + 1) + 113) * leeRows params Q =
      (42 * (params.weightedDegreeBound + 1) + 87 + 9) * leeRows params Q + 17 * leeRows params Q := by
    ring
  omega

theorem ofFn_val_size_le {n : ℕ} (f : Fin n → K) : (CPolynomial.ofFn f).val.size ≤ n :=
  ofFn_size_le f

/-- **The grid divided by the pivot** (`leeScaled`: per coefficient a division, the pivot
inverted each time): at most `(20015·(W + 1) + 152)·rows + 53`. -/
theorem leeScaledC_cost (hP : Includes P leeScaled.c628.costDeps) (params : GSInterpParams)
    (Q : CBivariate K) (c : K) {A : ℕ} (hs : NormSizes params A) (hQ : InnerLe Q.val A)
    (hQs : Q.val.size < 2 ^ 64) :
    machineCost P leeScaled.c628.costIdx [encodeValue params, encodeValue Q, encodeValue c] ≤
      (20015 * (params.weightedDegreeBound + 1) + 152) * leeRows params Q + 53 := by
  obtain ⟨hW, hk, hyW, hA⟩ := hs
  have hR := leeRows_le params Q
  rw [leeScaled.c628.costEq P hP]
  have := leeRowsC_cost P (by includes) params Q (by omega) hQs
  have hf := fun y ↦ RunsApp.of_spec (us := [encodeValue params, encodeValue Q, encodeValue c]) (vs := [encodeValue y])
    (leeScaled.c628.lam0.costSpec P (by includes) params Q c y)
  rw [Auto.CompPoly.CPolynomial.ofFn.c629.costEq P (by includes) _
    (.closure leeScaled.c628.lam0.costIdx [encodeValue params, encodeValue Q, encodeValue c]) hf]
  have hfr := ofFnFrom_cost P (by includes) (n := leeRows params Q) (by omega) _
    (.closure leeScaled.c628.lam0.costIdx [encodeValue params, encodeValue Q, encodeValue c]) hf
    (20012 * (params.weightedDegreeBound + 1) + 92) (fun y ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [leeScaled.c628.lam0.costEq P (by includes)]
      have hy := y.isLt
      have hyw : yWeight params * y < 2 ^ 64 := by
        have := Nat.mul_le_mul_left (yWeight params) (show (y : ℕ) ≤ params.weightedDegreeBound + 1
          by omega)
        omega
      have := leeColsC_cost P (by includes) params Q y (by omega) hk (by omega) hyw
        (by have := coeff_size_le_of_innerLe hQ y; omega)
      have hc := leeCols_le params Q y
      have hg := fun x ↦ RunsApp.of_spec (us := [encodeValue params, encodeValue Q, encodeValue c, encodeValue y]) (vs := [encodeValue x])
        (leeScaled.c628.lam0.lam0.costSpec P (by includes) params Q c y x)
      rw [Auto.CompPoly.CPolynomial.ofFn.c631.costEq P (by includes) _
        (.closure leeScaled.c628.lam0.lam0.costIdx [encodeValue params, encodeValue Q, encodeValue c, encodeValue y]) hg]
      have := ofFnFrom_cost P (by includes) (n := leeCols params Q y) (by omega) _
        (.closure leeScaled.c628.lam0.lam0.costIdx [encodeValue params, encodeValue Q, encodeValue c, encodeValue y]) hg 19970
        (fun x ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append]
          rw [leeScaled.c628.lam0.lam0.costEq P (by includes),
            Auto.CompPoly.CBivariate.coeff.c633.costEq P (by includes)]
          have := invK_cost P (by includes) c
          omega) 0 (by omega)
      have := ofArray_cost P (by includes)
        (Array.ofFn fun x : Fin (leeCols params Q y) ↦ Q.coeff ↑x ↑y / c) (by simp; omega)
      have h2 : (19970 + 18) * leeCols params Q y ≤ 19988 * (params.weightedDegreeBound + 1) :=
        Nat.mul_le_mul_left _ hc
      simp only [length_ofFnFrom, Array.size_ofFn, Nat.sub_zero] at *
      omega) 0 (by omega)
  have := ofArrayB_cost P (by includes)
    (Array.ofFn fun y : Fin (leeRows params Q) ↦
      CPolynomial.ofFn fun x : Fin (leeCols params Q y) ↦ Q.coeff ↑x ↑y / c)
    (params.weightedDegreeBound + 1)
    (fun x hx ↦ by
      obtain ⟨y, rfl⟩ := Array.mem_ofFn.1 hx
      exact (ofFn_val_size_le _).trans (leeCols_le params Q y))
    (by simp; omega)
  simp only [length_ofFnFrom, Array.size_ofFn, Nat.sub_zero] at *
  have e : (20015 * (params.weightedDegreeBound + 1) + 152) * leeRows params Q =
      (20012 * (params.weightedDegreeBound + 1) + 92 + 18) * leeRows params Q +
        (3 * (params.weightedDegreeBound + 1) + 41) * leeRows params Q + leeRows params Q := by
    ring
  omega

/-- **The normalization** (`normalizeLeeFast`: the pivot, then the grid divided by it): at most
`normBound W rows`, `Q` of at most `rows` rows. -/
theorem normalizeLeeFastC_cost (hP : Includes P normalizeLeeFast.c626.costDeps)
    (params : GSInterpParams) (Q : CBivariate K) {A rows : ℕ} (hs : NormSizes params A)
    (hQ : InnerLe Q.val A) (hQs : Q.val.size ≤ rows) (hrows : rows < 2 ^ 64) :
    machineCost P normalizeLeeFast.c626.costIdx [encodeValue params, encodeValue Q] ≤
      normBound params.weightedDegreeBound rows := by
  rw [normalizeLeeFast.c626.costEq P hP]
  have hp := leePivotC_cost P (by includes) params Q hs hQ (by omega)
  have hf := fun m ↦ RunsApp.of_spec (us := [encodeValue params, encodeValue Q]) (vs := [encodeValue m])
    (normalizeLeeFast.c626.lam0.costSpec P (by includes) params Q m)
  have := optionMap_cost P (by includes) _ (.closure normalizeLeeFast.c626.lam0.costIdx [encodeValue params, encodeValue Q])
    hf ((20015 * (params.weightedDegreeBound + 1) + 152) * leeRows params Q + 53 + 17)
    (leePivot? params Q) (fun m _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [normalizeLeeFast.c626.lam0.costEq P (by includes),
        Auto.CompPoly.CBivariate.coeff.c633.costEq P (by includes)]
      have := leeScaledC_cost P (by includes) params Q (Q.coeff m.xDegree m.yDegree) hs hQ
        (by omega)
      omega)
  have hR := (leeRows_le params Q).2
  have h1 : (42 * (params.weightedDegreeBound + 1) + 113) * leeRows params Q +
      (20015 * (params.weightedDegreeBound + 1) + 152) * leeRows params Q ≤
      (20057 * (params.weightedDegreeBound + 1) + 265) * rows := by
    have := Nat.mul_le_mul_left (20057 * (params.weightedDegreeBound + 1) + 265)
      (show leeRows params Q ≤ rows by omega)
    have e : (42 * (params.weightedDegreeBound + 1) + 113) * leeRows params Q +
        (20015 * (params.weightedDegreeBound + 1) + 152) * leeRows params Q =
        (20057 * (params.weightedDegreeBound + 1) + 265) * leeRows params Q := by ring
    omega
  unfold normBound
  omega

/-! ## The row as a polynomial -/

/-- **The row as a bivariate polynomial** (`ofCoeffRow`: trimmed): at most
`(3·A + 41)·w + 17`, `w` entries of at most `A` coefficients. -/
theorem ofCoeffRowC_cost (hP : Includes P ofCoeffRowC.costDeps)
    {w A : ℕ} (row : PolynomialRow K) (h : RowWithin w A row) (hw : w < 2 ^ 63) :
    machineCost P ofCoeffRowC.costIdx [encodeValue row] ≤
      (3 * A + 41) * w + 17 := by
  rw [ofCoeffRowC.costEq P hP]
  have := ofArrayB_cost P (by includes) row A h.2 (by have := h.1; omega)
  have := Nat.mul_le_mul_left (3 * A + 41) h.1
  omega

theorem ofCoeffRow_sizes {w A : ℕ} {row : PolynomialRow K} (h : RowWithin w A row) :
    (CBivariate.ofCoeffRow row).val.size ≤ w ∧ InnerLe (CBivariate.ofCoeffRow row).val A := by
  have hv : (CBivariate.ofCoeffRow row).val = CPolynomial.Raw.trim row := rfl
  rw [hv]
  exact ⟨(raw_trim_size_le _).trans h.1, InnerLe.trim h.2⟩

end

end LeanVM.Cost.Bounds.Decoder
