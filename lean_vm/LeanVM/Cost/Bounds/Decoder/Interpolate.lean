module

public import LeanVM.Cost.Bounds.Decoder.LeeRows
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic
import all CompPoly.Bivariate.CoeffRows
import all CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Algorithm
import all CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Basic

/-!
# Bound: the decoder's interpolation, compiled

The price of `interpolateDistinct points params` (`Fast/DecoderFast.lean`, compiled in
`Cost/Extractor/Interp.lean`) on `n` points, `k > 1`: Lee–O'Sullivan's basis reduced by
Mulders–Storjohann, then the least row normalized.

* the least row of the reduced matrix (`leastShiftedDegreeRowC_cost`: a shifted degree and a
  comparison per row), the row as a polynomial (`ofCoeffRowC_cost`);
* the normalization (`normalizeLeeFastC_cost`): the first nonzero coefficient of the grid
  (`leePivotC_cost`: at most `W + 1` coefficients tested per row) and every coefficient of the grid
  divided by it (`leeScaledC_cost`: an inverse per coefficient, see the note below);
* the assembly (`leeCoreC_cost`): the vanishing and interpolating polynomials
  (`Bounds/Decoder/Interp.lean`), the rows (`Bounds/Decoder/LeeRows.lean`), the reduction
  (`msReduceC_cost`, `Bounds/Decoder/MsReduce.lean`, on the basis's invariant `interpBasis_msInv`),
  the least row, its normalization: `interpCoreBound n m ℓ D S W`
  (`D = m·n + ℓ·(k − 1)`, `S = ℓ·(k − 1)`), and `interpolateDistinctC_cost`.

At the worst shape `(28, 4)` the lane's interpolation costs at most `≈ 2^111.67`
(`laneInterp_cost_28_4`), the reduction's `2^111.67` (`laneMsReduce_cost_28_4`) dominating; the rows
cost `≈ 2^98.25`, the rest below `2^60`.

**Honest-cost note.** `leeScaled` divides every coefficient of the grid by the pivot: the compiled
division inverts the pivot again for each coefficient (`invItohTsujii`, `≤ 19700`, against `258`
for a product), a constant factor `≈ 76` on the normalization, `≈ 2^58` at `(28, 4)`, far below
the reduction.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open CompPoly.GuruswamiSudan CompPoly.PolynomialMatrix

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.LeanVM.Extraction.Fast LeanVM.Cost.Auto.CompPoly.GuruswamiSudan.LeeOSullivan

public section

variable (P : Program)

/-! ## Library functions -/

theorem length_ofFnFrom {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) :
    (Rewrite.ofFnFrom f i).length = n - i := by
  rw [Rewrite.ofFnFrom_eq f (n - i) i rfl]
  simp

/-! ## The normalization -/

/-- `leeRows`: at most `15`. -/
theorem leeRowsC_cost (hP : Includes P leeRows.c123.costDeps) (params : GSInterpParams)
    (Q : CBivariate K) (hW : params.weightedDegreeBound + 1 < 2 ^ 64) (hQ : Q.val.size < 2 ^ 64) :
    machineCost P leeRows.c123.costIdx [enc params, enc Q] ≤ 15 := by
  rw [leeRows.c123.costEq P hP]
  cost_simp
  split_ifs <;> omega

/-- `leeCols` at row `y`: at most `50`. -/
theorem leeColsC_cost (hP : Includes P leeCols.c122.costDeps) (params : GSInterpParams)
    (Q : CBivariate K) (y : ℕ) (hW : params.weightedDegreeBound + 1 < 2 ^ 64)
    (hk : params.messageDegree < 2 ^ 64) (hy : y < 2 ^ 64) (hyw : yWeight params * y < 2 ^ 64)
    (hq : (Q.val.coeff y).val.size < 2 ^ 64) :
    machineCost P leeCols.c122.costIdx [enc params, enc Q, enc y] ≤ 50 := by
  have hyw' : yWeight params < 2 ^ 64 := by unfold yWeight; omega
  rw [leeCols.c122.costEq P hP]
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
theorem leePivotC_cost (hP : Includes P leePivot?.c124.costDeps) (params : GSInterpParams)
    (Q : CBivariate K) {A : ℕ} (hs : NormSizes params A) (hQ : InnerLe Q.val A)
    (hQs : Q.val.size < 2 ^ 64) :
    machineCost P leePivot?.c124.costIdx [enc params, enc Q] ≤
      (42 * (params.weightedDegreeBound + 1) + 113) * leeRows params Q + 35 := by
  obtain ⟨hW, hk, hyW, hA⟩ := hs
  have hR := leeRows_le params Q
  rw [leePivot?.c124.costEq P hP]
  have := leeRowsC_cost P (by includes) params Q (by omega) hQs
  have := rangeLoop_cost P (by includes) (leeRows params Q) [] (by omega)
  have hf := fun y ↦ RunsApp.of_spec (us := [enc params, enc Q]) (vs := [enc y])
    (leePivot?.c124.lam0.costSpec P (by includes) params Q y)
  have hfs := findSome_cost P (by includes) _ (.fn leePivot?.c124.lam0.costIdx [enc params, enc Q])
    hf (42 * (params.weightedDegreeBound + 1) + 87) (List.range (leeRows params Q)) (fun y hy ↦ by
      rw [List.mem_range] at hy
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [leePivot?.c124.lam0.costEq P (by includes)]
      have hyw : yWeight params * y < 2 ^ 64 := by
        have := Nat.mul_le_mul_left (yWeight params) (show y ≤ params.weightedDegreeBound + 1 by
          omega)
        omega
      have := leeColsC_cost P (by includes) params Q y (by omega) hk (by omega) hyw
        (by have := coeff_size_le_of_innerLe hQ y; omega)
      have hc := leeCols_le params Q y
      have := rangeLoop_cost P (by includes) (leeCols params Q y) [] (by omega)
      have hp := fun x ↦ RunsApp.of_spec (us := [enc Q, enc y]) (vs := [enc x])
        (leePivot?.c124.lam0.lam1.costSpec P (by includes) Q y x)
      have := findNat_cost P (by includes) _ (.fn leePivot?.c124.lam0.lam1.costIdx [enc Q, enc y])
        hp 16 (List.range (leeCols params Q y)) (fun x _ ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append]
          rw [leePivot?.c124.lam0.lam1.costEq P (by includes),
            Auto.CompPoly.CBivariate.coeff.c121.costEq P (by includes)])
      have hm := fun x ↦ RunsApp.of_spec (us := [enc y]) (vs := [enc x])
        (leePivot?.c124.lam0.lam0.costSpec P (by includes) y x)
      have := optionMap_cost P (by includes)
        (fun x ↦ ({ xDegree := x, yDegree := y } : CBivariate.Monomial))
        (.fn leePivot?.c124.lam0.lam0.costIdx [enc y]) hm
        5 ((List.range (leeCols params Q y)).find? fun x ↦ !Q.coeff x y == 0) (fun x _ ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append]
          rw [leePivot?.c124.lam0.lam0.costEq P (by includes)])
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
theorem leeScaledC_cost (hP : Includes P leeScaled.c115.costDeps) (params : GSInterpParams)
    (Q : CBivariate K) (c : K) {A : ℕ} (hs : NormSizes params A) (hQ : InnerLe Q.val A)
    (hQs : Q.val.size < 2 ^ 64) :
    machineCost P leeScaled.c115.costIdx [enc params, enc Q, enc c] ≤
      (20015 * (params.weightedDegreeBound + 1) + 152) * leeRows params Q + 53 := by
  obtain ⟨hW, hk, hyW, hA⟩ := hs
  have hR := leeRows_le params Q
  rw [leeScaled.c115.costEq P hP]
  have := leeRowsC_cost P (by includes) params Q (by omega) hQs
  have hf := fun y ↦ RunsApp.of_spec (us := [enc params, enc Q, enc c]) (vs := [enc y])
    (leeScaled.c115.lam0.costSpec P (by includes) params Q c y)
  rw [Auto.CompPoly.CPolynomial.ofFn.c116.costEq P (by includes) _
    (.fn leeScaled.c115.lam0.costIdx [enc params, enc Q, enc c]) hf]
  have hfr := ofFnFrom_cost P (by includes) (n := leeRows params Q) (by omega) _
    (.fn leeScaled.c115.lam0.costIdx [enc params, enc Q, enc c]) hf
    (20012 * (params.weightedDegreeBound + 1) + 92) (fun y ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [leeScaled.c115.lam0.costEq P (by includes)]
      have hy := y.isLt
      have hyw : yWeight params * y < 2 ^ 64 := by
        have := Nat.mul_le_mul_left (yWeight params) (show (y : ℕ) ≤ params.weightedDegreeBound + 1
          by omega)
        omega
      have := leeColsC_cost P (by includes) params Q y (by omega) hk (by omega) hyw
        (by have := coeff_size_le_of_innerLe hQ y; omega)
      have hc := leeCols_le params Q y
      have hg := fun x ↦ RunsApp.of_spec (us := [enc params, enc Q, enc c, enc y]) (vs := [enc x])
        (leeScaled.c115.lam0.lam0.costSpec P (by includes) params Q c y x)
      rw [Auto.CompPoly.CPolynomial.ofFn.c119.costEq P (by includes) _
        (.fn leeScaled.c115.lam0.lam0.costIdx [enc params, enc Q, enc c, enc y]) hg]
      have := ofFnFrom_cost P (by includes) (n := leeCols params Q y) (by omega) _
        (.fn leeScaled.c115.lam0.lam0.costIdx [enc params, enc Q, enc c, enc y]) hg 19970
        (fun x ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append]
          rw [leeScaled.c115.lam0.lam0.costEq P (by includes),
            Auto.CompPoly.CBivariate.coeff.c121.costEq P (by includes)]
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
theorem normalizeLeeFastC_cost (hP : Includes P normalizeLeeFast.c113.costDeps)
    (params : GSInterpParams) (Q : CBivariate K) {A rows : ℕ} (hs : NormSizes params A)
    (hQ : InnerLe Q.val A) (hQs : Q.val.size ≤ rows) (hrows : rows < 2 ^ 64) :
    machineCost P normalizeLeeFast.c113.costIdx [enc params, enc Q] ≤
      normBound params.weightedDegreeBound rows := by
  rw [normalizeLeeFast.c113.costEq P hP]
  have hp := leePivotC_cost P (by includes) params Q hs hQ (by omega)
  have hf := fun m ↦ RunsApp.of_spec (us := [enc params, enc Q]) (vs := [enc m])
    (normalizeLeeFast.c113.lam0.costSpec P (by includes) params Q m)
  have := optionMap_cost P (by includes) _ (.fn normalizeLeeFast.c113.lam0.costIdx [enc params, enc Q])
    hf ((20015 * (params.weightedDegreeBound + 1) + 152) * leeRows params Q + 53 + 17)
    (leePivot? params Q) (fun m _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [normalizeLeeFast.c113.lam0.costEq P (by includes),
        Auto.CompPoly.CBivariate.coeff.c121.costEq P (by includes)]
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

/-! ## The least row -/

/-- The scan's invariant: the best row so far is the matrix's row at its index, below the
matrix's size, its degree at most `B`. -/
@[expose] def BestInv (M : PolynomialMatrix K) (B : ℕ)
    (best : Option (LeeOSullivan.RowChoice K)) : Prop :=
  ∀ c, best = some c → c.row = M.getD c.index #[] ∧ c.index < M.size ∧ c.degree ≤ B

theorem bestInv_step {M : PolynomialMatrix K} {shift : Array ℕ} {B : ℕ}
    (hB : ∀ i d, rowShiftedDegree? (M.getD i #[]) shift = some d → d ≤ B)
    {best : Option (LeeOSullivan.RowChoice K)} (h : BestInv M B best) {i : ℕ} (hi : i < M.size) :
    BestInv M B (LeeOSullivan.leastShiftedDegreeRowStep? M shift best i) := by
  intro c hc
  unfold LeeOSullivan.leastShiftedDegreeRowStep? at hc
  generalize hrow : M.getD i #[] = row at hc
  dsimp only at hc
  cases hd : rowShiftedDegree? row shift with
  | none => rw [hd] at hc; exact h c hc
  | some d =>
    rw [hd] at hc
    dsimp only at hc
    have hdB := hB i d (hrow ▸ hd)
    cases best with
    | none => cases hc; exact ⟨hrow.symm, hi, hdB⟩
    | some cur =>
      dsimp only at hc
      split_ifs at hc
      · cases hc; exact ⟨hrow.symm, hi, hdB⟩
      · exact h c hc

theorem bestInv_foldl {M : PolynomialMatrix K} {shift : Array ℕ} {B : ℕ}
    (hB : ∀ i d, rowShiftedDegree? (M.getD i #[]) shift = some d → d ≤ B) :
    ∀ (l : List ℕ) (best : Option (LeeOSullivan.RowChoice K)), (∀ i ∈ l, i < M.size) →
      BestInv M B best → BestInv M B (l.foldl (LeeOSullivan.leastShiftedDegreeRowStep? M shift) best) := by
  intro l
  induction l with
  | nil => intro best _ h; exact h
  | cons i l ih =>
    intro best hl h
    exact ih _ (fun j hj ↦ hl j (by simp [hj])) (bestInv_step hB h (hl i (by simp)))

/-- **The least row is a row of the matrix**: under the invariant, of width `w` and entries of
at most `D + 1` coefficients. -/
theorem leastShiftedDegreeRow?_rowWithin {r w D S : ℕ} {M : PolynomialMatrix K}
    {shift : Array ℕ} (hM : MsInv r w D M shift) (hS : ∀ j, shift.getD j 0 ≤ S)
    {row : PolynomialRow K} (h : LeeOSullivan.leastShiftedDegreeRow? M shift = some row) :
    RowWithin w (D + 1) row := by
  have hB : ∀ i d, rowShiftedDegree? (M.getD i #[]) shift = some d → d ≤ D + 1 + S :=
    fun i d hd ↦ rowShiftedDegree?_le (rowWithin_of_msInv hM i) hS hd
  have hinv := bestInv_foldl hB (List.range M.size) none (fun i hi ↦ List.mem_range.1 hi)
    (fun c hc ↦ by cases hc)
  unfold LeeOSullivan.leastShiftedDegreeRow? LeeOSullivan.leastShiftedDegreeChoice? at h
  cases hc : (List.range M.size).foldl (LeeOSullivan.leastShiftedDegreeRowStep? M shift) none with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h hinv
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    rw [(hinv c rfl).1]
    exact rowWithin_of_msInv hM c.index

/-- A comparison of two row choices: at most `30`. -/
theorem betterRowChoiceC_cost (hP : Includes P betterRowChoice.c111.costDeps)
    (a b : LeeOSullivan.RowChoice K) (ha : a.degree < 2 ^ 64) (hb : b.degree < 2 ^ 64)
    (hia : a.index < 2 ^ 64) (hib : b.index < 2 ^ 64) :
    machineCost P betterRowChoice.c111.costIdx [enc a, enc b] ≤ 30 := by
  rw [betterRowChoice.c111.costEq P hP]
  cost_simp
  split_ifs <;> omega

/-- One step of the scan: at most `90·w + 100`. -/
theorem rowStepC_cost (hP : Includes P leastShiftedDegreeRowStep?.c110.costDeps) {r w D S : ℕ}
    (hw : w < 2 ^ 62) (hDS : D + 1 + S < 2 ^ 62) (M : PolynomialMatrix K) (shift : Array ℕ)
    (hS : ∀ j, shift.getD j 0 ≤ S) (hM : MsInv r w D M shift)
    (best : Option (LeeOSullivan.RowChoice K)) (hbest : BestInv M (D + 1 + S) best)
    (hMs : M.size < 2 ^ 64) (i : ℕ) (hi : i < 2 ^ 64) :
    machineCost P leastShiftedDegreeRowStep?.c110.costIdx [enc M, enc shift, enc best, enc i] ≤
      90 * w + 100 := by
  rw [leastShiftedDegreeRowStep?.c110.costEq P hP]
  have := rowShiftedDegree_cost P (by includes) hw (by omega) (M.getD i #[])
    (rowWithin_of_msInv hM i) shift hS
  generalize hd : rowShiftedDegree? (M.getD i #[]) shift = o
  cases o with
  | none => dsimp only; omega
  | some d =>
    have hdB := rowShiftedDegree?_le (rowWithin_of_msInv hM i) hS hd
    cases best with
    | none => dsimp only; omega
    | some cur =>
      obtain ⟨-, hci, hcd⟩ := hbest cur rfl
      have := betterRowChoiceC_cost P (by includes) { index := i, row := M.getD i #[], degree := d }
        cur (by dsimp only; omega) (by omega) hi (by omega)
      dsimp only
      split_ifs <;> omega

/-- **The least row** (`leastShiftedDegreeRow?`: the scan over `r` rows): at most
`(90·w + 140)·r + 40`. -/
theorem leastShiftedDegreeRowC_cost (hP : Includes P leastShiftedDegreeRow?.c105.costDeps)
    {r w D S : ℕ} (hr : r < 2 ^ 62) (hw : w < 2 ^ 62) (hDS : D + 1 + S < 2 ^ 62)
    (M : PolynomialMatrix K) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S)
    (hM : MsInv r w D M shift) :
    machineCost P leastShiftedDegreeRow?.c105.costIdx [enc M, enc shift] ≤
      (90 * w + 140) * r + 40 := by
  have hMr : M.size = r := hM.1
  have hB : ∀ i d, rowShiftedDegree? (M.getD i #[]) shift = some d → d ≤ D + 1 + S :=
    fun i d hd ↦ rowShiftedDegree?_le (rowWithin_of_msInv hM i) hS hd
  rw [leastShiftedDegreeRow?.c105.costEq P hP, leastShiftedDegreeChoice?.c108.costEq P (by includes)]
  have := rangeLoop_cost P (by includes) M.size [] (by omega)
  have hf := listFoldl_le P (by includes) _
    (.fn leastShiftedDegreeChoice?.c108.lam0.costIdx [enc M, enc shift])
    (fun best i ↦ RunsApp.of_spec (us := [enc M, enc shift]) (vs := [enc best, enc i])
      (leastShiftedDegreeChoice?.c108.lam0.costSpec P (by includes) M shift best i))
    (90 * w + 105) (BestInv M (D + 1 + S)) (List.range M.size) none (fun c hc ↦ by cases hc)
    (fun best hbest i hi ↦ by
      rw [List.mem_range] at hi
      refine ⟨bestInv_step hB hbest hi, ?_⟩
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [leastShiftedDegreeChoice?.c108.lam0.costEq P (by includes)]
      have := rowStepC_cost P (by includes) hw hDS M shift hS hM best hbest (by omega) i (by omega)
      omega)
  have hm := fun c ↦ RunsApp.of_spec (us := []) (vs := [enc c])
    (leastShiftedDegreeRow?.c105.lam0.costSpec P (by includes) c)
  have := optionMap_cost P (by includes) _ (.fn leastShiftedDegreeRow?.c105.lam0.costIdx []) hm 2
    (LeeOSullivan.leastShiftedDegreeChoice? M shift) (fun c _ ↦ by
      simp only [appCost_fn, List.nil_append]
      rw [leastShiftedDegreeRow?.c105.lam0.costEq P (by includes)])
  simp only [List.length_range] at hf
  simp only [hMr] at *
  have e : (90 * w + 140) * r = (90 * w + 105 + 9) * r + 26 * r := by ring
  omega

/-- **The row as a bivariate polynomial** (`ofCoeffRow`: trimmed): at most
`(3·A + 41)·w + 17`, `w` entries of at most `A` coefficients. -/
theorem ofCoeffRowC_cost (hP : Includes P Auto.CompPoly.CBivariate.ofCoeffRow.c112.costDeps)
    {w A : ℕ} (row : PolynomialRow K) (h : RowWithin w A row) (hw : w < 2 ^ 63) :
    machineCost P Auto.CompPoly.CBivariate.ofCoeffRow.c112.costIdx [enc row] ≤
      (3 * A + 41) * w + 17 := by
  rw [Auto.CompPoly.CBivariate.ofCoeffRow.c112.costEq P hP]
  have := ofArrayB_cost P (by includes) row A h.2 (by have := h.1; omega)
  have := Nat.mul_le_mul_left (3 * A + 41) h.1
  omega

theorem ofCoeffRow_sizes {w A : ℕ} {row : PolynomialRow K} (h : RowWithin w A row) :
    (CBivariate.ofCoeffRow row).val.size ≤ w ∧ InnerLe (CBivariate.ofCoeffRow row).val A := by
  have hv : (CBivariate.ofCoeffRow row).val = CPolynomial.Raw.trim row := rfl
  rw [hv]
  exact ⟨(raw_trim_size_le _).trans h.1, InnerLe.trim h.2⟩

/-! ## The assembly -/

/-- Lee–O'Sullivan's shifts: `shift[j] = j·(k − 1)` for the `ℓ + 1` columns, at most `ℓ·(k − 1)`. -/
theorem leeShifts_le (params : GSInterpParams) (j : ℕ) :
    (leeOSullivanShifts params).getD j 0 ≤ interpolationYCap params * yWeight params := by
  unfold leeOSullivanShifts leeOSullivanWidth
  by_cases hj : j < interpolationYCap params + 1
  · rw [weightedDegreeShift_getD _ _ _ hj]
    exact Nat.mul_le_mul_right _ (by omega)
  · simp [CBivariate.weightedDegreeShift, Array.getD_eq_getD_getElem?, Nat.not_lt.1 hj]

/-- **Lee–O'Sullivan's interpolation, compiled** (`leeOSullivanPositiveCoreFast`, the decoder's
contexts): on `n` points, at most `interpCoreBound n m (ℓ + 1) D W`, `D = m·n + ℓ·(k − 1)`. -/
theorem leeCoreC_cost (hP : Includes P leeOSullivanPositiveCoreFast.c73.costDeps)
    (points : Array (K × K)) (params : GSInterpParams) (hs : InterpSizes points.size params) :
    machineCost P leeOSullivanPositiveCoreFast.c73.costIdx [enc points, enc params] ≤
      interpCoreBound points.size params.multiplicity (interpolationYCap params + 1)
        (params.multiplicity * points.size + interpolationYCap params * yWeight params)
        params.weightedDegreeBound := by
  obtain ⟨hn, hW, hk, hyW, hw, hm, hmn, hDS, hfuel⟩ := hs
  have hV : vanishingContextFast.vanishingPolynomial = (vanishingFast : Array K → CPolynomial K) :=
    rfl
  have hRed : (muldersStorjohannFastReducerContext K).reduce = muldersStorjohannReduceFast := rfl
  rw [leeOSullivanPositiveCoreFast.c73.costEq P hP, hV, hRed]
  -- the values
  have hGd := vanishingFast_natDegree_le (points.map fun p ↦ p.1)
  have hGs := vanishingFast_size_le (points.map fun p ↦ p.1)
  simp only [Array.size_map] at hGd hGs
  have hRd : (CPolynomial.interpolateCoefficientFormWithVanishing
      (CPolynomial.BatchEvalContext.horner K) (vanishingFast (points.map fun p ↦ p.1))
      points).natDegree ≤ points.size := by
    have := interpolate_natDegree_le_pred (CPolynomial.BatchEvalContext.horner K)
      (vanishingFast (points.map fun p ↦ p.1)) points
    omega
  have hMinv := interpBasis_msInv (CPolynomial.BatchEvalContext.horner K) points params
  have hMred := muldersStorjohannReduceFast_msInv hMinv
  have hS := leeShifts_le params
  -- the prices
  have hf := fun pt ↦ RunsApp.of_spec (us := []) (vs := [enc pt])
    (leeOSullivanPositiveCoreFast.c73.lam0.costSpec P (by includes) pt)
  have hm1 := listMap_le P Auto.List.map.c12.costIdx
    (.fn leeOSullivanPositiveCoreFast.c73.lam0.costIdx [])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) 2 points.toList
    (fun pt _ ↦ by
      rw [appCost_fn, List.nil_append,
        leeOSullivanPositiveCoreFast.c73.lam0.costEq P (by includes)])
  have hvan := vanishingC_cost P (by includes) (points.map fun p ↦ p.1) (by simp; omega)
  have hint := interpolateC_cost P (by includes) (vanishingFast (points.map fun p ↦ p.1)) points
    (by omega) (by omega)
  have hGn : (vanishingFast (points.map fun p ↦ p.1)).val.size * points.size ≤
      (points.size + 1) * points.size := Nat.mul_le_mul_right _ hGs
  have hrows := leeRowsFastC_cost P (by includes) _ _ params hRd hGd hk (by omega)
    (by unfold yWeight; omega) hw hm hmn
  have hrl := rangeLoop_cost P (by includes) (leeOSullivanWidth params) [] (by
    unfold leeOSullivanWidth; omega)
  have hf1 := fun j ↦ RunsApp.of_spec (us := [enc params]) (vs := [enc j])
    (leeOSullivanPositiveCoreFast.c73.lam1.costSpec P (by includes) params j)
  have hm2 := listMap_le P Auto.List.map.c12.costIdx
    (.fn leeOSullivanPositiveCoreFast.c73.lam1.costIdx [enc params])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf1)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf1) 8
    (List.range (leeOSullivanWidth params))
    (fun j hj ↦ by
      rw [List.mem_range] at hj
      unfold leeOSullivanWidth at hj
      rw [appCost_fn, List.singleton_append,
        leeOSullivanPositiveCoreFast.c73.lam1.costEq P (by includes)]
      have : yWeight params < 2 ^ 64 := by unfold yWeight; omega
      cost_simp
      omega)
  have hms := msReduceC_cost P (by includes) (by omega) (by omega) hDS hfuel _ _ hS hMinv
  have hlr := leastShiftedDegreeRowC_cost P (by includes) (by omega) (by omega) (by omega) _ _ hS
    hMred
  have hwid : leeOSullivanWidth params = interpolationYCap params + 1 := rfl
  have hyw64 : yWeight params < 2 ^ 64 := by unfold yWeight; omega
  simp only [Array.length_toList, List.length_map, List.length_range, Array.size_map, hwid] at *
  cost_simp
  -- the least row
  generalize hlo : LeeOSullivan.leastShiftedDegreeRow? (muldersStorjohannReduceFast
    (leeRowsFast (CPolynomial.interpolateCoefficientFormWithVanishing
      (CPolynomial.BatchEvalContext.horner K) (vanishingFast (points.map fun p ↦ p.1)) points)
      (vanishingFast (points.map fun p ↦ p.1)) params) (leeOSullivanShifts params))
    (leeOSullivanShifts params) = lo
  cases lo with
  | none =>
    dsimp only
    unfold interpCoreBound
    omega
  | some row =>
    have hrow := leastShiftedDegreeRow?_rowWithin hMred hS hlo
    have hrd := rowShiftedDegree_cost P (by includes) (by omega) (by omega) row hrow
      (leeOSullivanShifts params) hS
    dsimp only
    generalize hdo : rowShiftedDegree? row (leeOSullivanShifts params) = dd
    cases dd with
    | none =>
      dsimp only
      unfold interpCoreBound
      omega
    | some d =>
      have hd := rowShiftedDegree?_le hrow hS hdo
      have hoc := ofCoeffRowC_cost P (by includes) row hrow (by omega)
      have hQ := ofCoeffRow_sizes hrow
      have hnorm := normalizeLeeFastC_cost P (by includes) params (CBivariate.ofCoeffRow row)
        (A := _) (rows := interpolationYCap params + 1) ⟨hW, hk, hyW, by omega⟩ hQ.2 hQ.1
        (by omega)
      dsimp only
      cost_simp
      split_ifs
      · generalize normalizeLeeFast params (CBivariate.ofCoeffRow row) = no
        cases no <;> dsimp only <;> unfold interpCoreBound <;> omega
      · unfold interpCoreBound
        omega

/-- **The decoder's interpolation, compiled** (`interpolateDistinct`, `k > 1`): at most
`interpCoreBound n m (ℓ + 1) D W + 10`. -/
theorem interpolateDistinctC_cost (hP : Includes P interpolateDistinctC.costDeps)
    (points : Array (K × K)) (params : GSInterpParams) (hs : InterpSizes points.size params)
    (hk1 : 1 < params.messageDegree) :
    machineCost P interpolateDistinctC.costIdx [enc points, enc params] ≤
      interpCoreBound points.size params.multiplicity (interpolationYCap params + 1)
        (params.multiplicity * points.size + interpolationYCap params * yWeight params)
        params.weightedDegreeBound + 10 := by
  have hk := hs.2.2.1
  rw [interpolateDistinctC.costEq P hP]
  have := leeCoreC_cost P (by includes) points params hs
  have hk' : ¬ params.messageDegree ≤ 1 := by omega
  simp only [hk', ↓reduceIte]
  cost_simp
  omega


/-! ## On a lane -/

open LeanVM.Extraction in
/-- The bound of a lane's interpolation at the decoder's parameters (`n = 2^(κ+R)` points). -/
@[expose] def laneInterpBound (κ R A : ℕ) : ℕ :=
  interpCoreBound (2 ^ (κ + R)) (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.multiplicity
    (interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp + 1)
    ((gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.multiplicity * 2 ^ (κ + R) +
      interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp *
        yWeight (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp)
    (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.weightedDegreeBound + 10

open LeanVM.Extraction in
/-- **A lane's interpolation** (`interpolateDistinct` on the lane's points, the decoder's
parameters): at most `laneInterpBound κ R A`, when the sizes are word-sized and `k > 1`. -/
theorem laneInterp_cost (hP : Includes P interpolateDistinctC.costDeps) (κ R A : ℕ)
    (S : ℕ → ℕ → K) (u : ℕ)
    (hs : InterpSizes (2 ^ (κ + R)) (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp)
    (hk1 : 1 < (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.messageDegree) :
    machineCost P interpolateDistinctC.costIdx
        [enc (lanePointsS (2 ^ (κ + R)) S u), enc (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp] ≤
      laneInterpBound κ R A := by
  have := interpolateDistinctC_cost P hP (lanePointsS (2 ^ (κ + R)) S u) _
    (by rwa [lanePointsS_size]) hk1
  rwa [lanePointsS_size] at this

open LeanVM.Extraction in
/-- **At the worst shape `(28, 4)`** (`k = 2^22`, `n = 2^26`, `A = 16792398`: `m = 415`,
`ℓ = 1661`, `W = 6968845169`): a lane's interpolation costs at most
`4121135194401974193367341077651775 ≈ 2^111.67`, the reduction (`laneMsReduce_cost_28_4`,
`≈ 2^111.67`) all but `≈ 2^98.25` of it (the rows, `leeRowsBound`). -/
theorem laneInterp_cost_28_4 (hP : Includes P interpolateDistinctC.costDeps) (S : ℕ → ℕ → K)
    (u : ℕ) :
    machineCost P interpolateDistinctC.costIdx
        [enc (lanePointsS (2 ^ (22 + 4)) S u),
          enc (gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp] ≤
      4121135194401974193367341077651775 := by
  have := laneInterp_cost P hP 22 4 16792398 S u (by unfold InterpSizes; decide +kernel)
    (by decide +kernel)
  have h : laneInterpBound 22 4 16792398 = 4121135194401974193367341077651775 := by
    decide +kernel
  omega

/-- The rows' share at `(28, 4)`: `leeRowsBound 415 1662 2^26 ≈ 2^98.25`. -/
theorem leeRowsBound_28_4 :
    leeRowsBound 415 1662 (2 ^ 26) = 376307019475782358420478783011 := by decide +kernel

end

end LeanVM.Cost.Bounds.Decoder
