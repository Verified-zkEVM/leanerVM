module

public import LeanVM.Cost.Bounds.PMCore.Glue
public import LeanVM.Cost.Bounds.PMCore.Products
public import LeanVM.Cost.Bounds.PMBasis.Recursion
public import LeanVM.Protocol.Extraction.Fast.PMBasis.DegreeRecursion
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.XAdicSoundness
import all CompPoly.LinearAlgebra.PolynomialMatrix.Operations
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.Basic

/-!
# Bounds: the PM-basis core, compiled

`pmCoreC` (`Cost/Extractor/PMCore.lean`) is CompPoly's `pmBasisWithFuelCore` on the target
runtime `popovEvalRuntime novelTransform fftMulContext fftMulLowContext 1` (the ordered-weak-Popov
leaf at order one, the evaluation-domain products). Its price, by its two equations
(`pmCoreC.costEq_zero`, `pmCoreC.costEq_succ`) through the model's recursion
(`pmBasisWithFuelCore_price_le`, `Bounds/PMBasis/Recursion.lean`):

* **`residualMatrixC_cost`**: the residual `(P₁·A) div X^d`: the column-truncated product
  (`MulTruncEvalPCost`, track fft's) and `R·W` entries of at most `59·O + 87` each;
* **`pmCoreC_node`**: a node's own price at maximal order `o` is at most
  `pmNodePrice p r m o` (`p.ovh ≥ 80`), the products within `evalMatPrice`, the sizes from
  `popovRuntime_core_node` (exactly `r` rows, degrees at most the halves' orders);
* **`pmCoreC_cost`**: on a problem of `r ≥ m` rows of width `m` (`CoreInv`: shifts plus twice the
  maximal order at most `SB < 2^60`), at the fuel `pmBasisFuel = maxOrder + 1`, the price is at
  most `pmTree 1 L (pmNodePrice p r m) (maxOrder problem)`, `L` the leaf's price (`LeafCost`: the
  ordered-weak-Popov leaf and its compaction within `Lc`) and `18·m + 100`.
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Cost.Bounds.Decoder LeanVM.Cost.Bounds.PMBasis
open LeanVM.Extraction.Fast LeanVM.Extraction.Fast.FFT
open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

/-! ## The products' shapes -/

theorem rowWithin_empty (C D : ℕ) : RowWithin C D (#[] : PolynomialRow K) :=
  ⟨by simp, by simp⟩

theorem mulTruncEvalP_size (ords : Array ℕ) (A B : PolynomialMatrix K) :
    (mulTruncEvalP novelTransform fftMulContext ords A B).size = A.size := by
  rw [mulTruncEvalP_eq, EvalMat.mulTruncEval_eq_truncateColumns _ _ fftMulContext,
    truncateColumns_size, mulWith_size]

theorem mulTruncEvalP_width_le (ords : Array ℕ) (A B : PolynomialMatrix K) :
    MatrixWidth (mulTruncEvalP novelTransform fftMulContext ords A B) ≤ MatrixWidth B := by
  rw [mulTruncEvalP_eq, EvalMat.mulTruncEval_eq_truncateColumns _ _ fftMulContext,
    PMDegree.matrixWidth_eq_getD_size']
  rcases Nat.eq_zero_or_pos A.size with h0 | hpos
  · have : (truncateColumns ords (mulWith fftMulContext A B)).size = 0 := by
      rw [truncateColumns_size, mulWith_size, h0]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simp
  · rw [truncateColumns_getD _ _ (by rw [mulWith_size]; exact hpos), mulWith_getD _ _ _ hpos]
    simp [rowTruncateColumns, rowMulMatrixWith_size]

/-- The composition `A·B` (`mulEvalP`): `|A|` rows of at most `width B` entries of at most
`dA + dB + 1` coefficients. -/
theorem mulEvalP_shape (A B : PolynomialMatrix K) {dA dB : ℕ} (hA : DegLe A dA) (hB : DegLe B dB) :
    (mulEvalP novelTransform fftMulContext A B).size = A.size ∧
      ∀ i, RowWithin (MatrixWidth B) (dA + dB + 1)
        ((mulEvalP novelTransform fftMulContext A B).getD i #[]) := by
  rw [mulEvalP_eq, EvalMat.mulEval_eq_mulWith _ _ fftMulContext]
  refine ⟨mulWith_size _ _ _, fun i ↦ ?_⟩
  rcases Nat.lt_or_ge i A.size with hi | hi
  · rw [mulWith_getD _ _ _ hi]
    refine ⟨by rw [rowMulMatrixWith_size], fun e he ↦ ?_⟩
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem he
    have hd := PMDegree.natDegree_rowGet_rowMulMatrixWith_le fftMulContext (A.getD i #[]) B
      (a := dA) (b := dB) (fun k ↦ hA i k) (fun r hr j ↦ by
        rw [MatrixRows] at hr
        obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hr
        have e : B.toList[l] = B.getD l #[] := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hl)]; simp
        rw [e]; exact hB l j) j
    have hrg : rowGet (rowMulMatrixWith fftMulContext (A.getD i #[]) B) j =
        (rowMulMatrixWith fftMulContext (A.getD i #[]) B)[j] := by
      rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]; rfl
    rw [hrg] at hd
    have := PMDegree.val_size_le_natDegree_add_one
      (rowMulMatrixWith fftMulContext (A.getD i #[]) B)[j]
    omega
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [mulWith_size]; omega)]
    exact rowWithin_empty _ _

/-! ## The residual matrix -/

variable (P : MachineProgram)

/-- **The residual** `(P₁·A) div X^d` truncated at `orders` (`residualMatrixC`): the
column-truncated product, then `|P₁|·width` entries, each at most `59·O + 87` (`O` the residual
orders' bound). -/
theorem residualMatrixC_cost (hP : Includes P residualMatrixC.costDeps)
    (basis matrix : PolynomialMatrix K) (d : ℕ) (orders : Array ℕ) {O : ℕ}
    (hO : ∀ j, orders.getD j 0 ≤ O) (hdO : d + O < 2 ^ 62)
    (hbs : basis.size < 2 ^ 62) (hmw : MatrixWidth matrix < 2 ^ 62) :
    machineCost P residualMatrixC.costIdx
        [encodeValue basis, encodeValue matrix, encodeValue d, encodeValue orders] ≤
      19 * orders.size + 60 +
        machineCost P mulTruncEvalPC.costIdx [encodeValue (orders.map fun order ↦ order + d),
          encodeValue basis, encodeValue matrix] +
        basis.size * ((59 * O + 87) * MatrixWidth matrix + 66) := by
  rw [residualMatrixC.costEq P hP]
  have hord : ∀ x ∈ orders, x ≤ O := fun x hx ↦ by
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hx
    have := hO j
    rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj] at this
  have hm := map_cost P (by includes) (fun order : ℕ ↦ order + d)
    (.closure residualMatrixC.lam0.costIdx [encodeValue d])
    (fun a ↦ RunsApp.of_spec (residualMatrixC.lam0.costSpec P (by includes) d a)) 4
    orders.toList (fun a ha ↦ by
      have := hord a (by simpa using ha)
      rw [appCost_fn, List.singleton_append, residualMatrixC.lam0.costEq P (by includes),
        limbs_of_lt (by omega : a < 2 ^ 64), limbs_of_lt (by omega : d < 2 ^ 64)]
      simp)
  set prod := mulTruncEvalP novelTransform fftMulContext (orders.map fun order ↦ order + d)
    basis matrix with hprod
  have hps : prod.size = basis.size := mulTruncEvalP_size _ _ _
  have hpw : MatrixWidth prod ≤ MatrixWidth matrix := mulTruncEvalP_width_le _ _ _
  have hw := matrixWidthC_cost P (by includes) prod (by omega)
  have hf := fun a b ↦ RunsApp.of_spec (us := [encodeValue d, encodeValue orders, encodeValue prod])
    (vs := [encodeValue a, encodeValue b]) (residualMatrixC.lam1.costSpec P (by includes) d orders prod a b)
  have hof := ofFnC_cost P (by includes) prod.size (MatrixWidth prod) (by omega) (by omega) _
    (.closure residualMatrixC.lam1.costIdx [encodeValue d, encodeValue orders, encodeValue prod])
    hf (59 * O + 54) (fun i _ j _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [residualMatrixC.lam1.costEq P (by includes), rowGet_cost P (by includes)]
      have := divXTruncC_cost P (by includes) d (orders.getD j 0)
        (rowGet (prod.getD i #[]) j) (by have := hO j; omega)
      have := hO j
      omega)
  have h1 : (59 * O + 54 + 33) * MatrixWidth prod ≤ (59 * O + 87) * MatrixWidth matrix :=
    Nat.mul_le_mul_left _ hpw
  have h2 : prod.size * ((59 * O + 54 + 33) * MatrixWidth prod + 66) ≤
      basis.size * ((59 * O + 87) * MatrixWidth matrix + 66) := by
    rw [hps]; exact Nat.mul_le_mul_left _ (by omega)
  simp only [Array.length_toList, List.length_map] at hm ⊢
  omega


/-! ## The recursion on the target runtime -/

/-- The target runtime: the ordered-weak-Popov PM-basis on evaluation-domain products, cutoff `1`. -/
abbrev targetRT : PMBasisRuntime K := popovEvalRuntime novelTransform fftMulContext fftMulLowContext 1

theorem targetRT_eq : targetRT = Popov.popovRuntime fftMulContext fftMulLowContext 1 1 :=
  popovEvalRuntime_eq _ _ _ 1 1

/-- **The invariant** of the problems the recursion visits: `r` rows of width `m`, at most `m`
orders, word-sized entries, the shifts plus twice the maximal order at most `SB`. -/
@[expose] def CoreInv (r m SB : ℕ) (problem : XAdicProblem K) (shift : Array ℕ) : Prop :=
  problem.matrix.size = r ∧ (∀ row ∈ problem.matrix.toList, row.size = m) ∧
    problem.orders.size ≤ m ∧ SizeLe problem.matrix (2 ^ 62) ∧
    ∀ j, shift.getD j 0 + 2 * maxOrder problem ≤ SB

/-- **The leaf's price**: the ordered-weak-Popov leaf at order at most one and its compaction,
within `Lc`, on the invariant's problems. -/
@[expose] def LeafCost (P : MachineProgram) (r m SB Lc : ℕ) : Prop :=
  ∀ problem shift, CoreInv r m SB problem shift → maxOrder problem ≤ 1 →
    machineCost P popovLeafC.costIdx [encodeValue problem, encodeValue shift] +
      machineCost P compactNonzeroRowsC.costIdx [encodeValue (Popov.popovLeafBasis problem shift)] ≤
        Lc

theorem le_maxOrder (problem : XAdicProblem K) : ∀ x ∈ problem.orders, x ≤ maxOrder problem := by
  intro x hx
  unfold maxOrder
  rw [← Array.foldl_toList]
  have hx' : x ∈ problem.orders.toList := by simpa using hx
  suffices h : ∀ (l : List ℕ) (a : ℕ), x ∈ l → x ≤ l.foldl max a from h _ 0 hx'
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons y l ih =>
    intro a h
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · have : ∀ (l : List ℕ) (b : ℕ), b ≤ l.foldl max b := by
        intro l; induction l with
        | nil => intro b; simp
        | cons z l ih' => intro b; exact (le_max_left b z).trans (ih' _)
      exact (le_max_right a x).trans (this l _)
    · exact ih _ h

theorem getD_le_of_mem {a : Array ℕ} {B j : ℕ} (h : ∀ x ∈ a, x ≤ B) : a.getD j 0 ≤ B := by
  rw [Array.getD_eq_getD_getElem?]
  cases hj : a[j]? with
  | none => simp
  | some x => exact h x (Array.mem_of_getElem? hj)

theorem rowWithin_of_rows {M : PolynomialMatrix K} {C D : ℕ}
    (hsz : ∀ row ∈ M.toList, row.size ≤ C) (hD : SizeLe M D) (i : ℕ) : RowWithin C D (M.getD i #[]) := by
  rcases Nat.lt_or_ge i M.size with hi | hi
  · have hmem : M.getD i #[] ∈ M.toList := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]; simp
    refine ⟨hsz _ hmem, fun e he ↦ ?_⟩
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem he
    have := hD i j
    rwa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj] at this
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    exact rowWithin_empty _ _

/-- The updated shift: at most `X` where every row's shifted degree and every shift is. -/
theorem updateShiftByRows_getD_le (B : PolynomialMatrix K) (shift : Array ℕ) {X : ℕ}
    (hrow : ∀ i v, rowShiftedDegree? (B.getD i #[]) shift = some v → v ≤ X)
    (hs : ∀ j, shift.getD j 0 ≤ X) (j : ℕ) : (updateShiftByRows B shift).getD j 0 ≤ X := by
  unfold updateShiftByRows
  rw [Array.getD_eq_getD_getElem?]
  rcases Nat.lt_or_ge j B.size with hj | hj
  · rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hj]
    simp only [Option.map_some, Option.getD_some]
    cases hv : rowShiftedDegree? (B.getD j #[]) shift with
    | none => exact hs j
    | some v => exact hrow j v hv
  · rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_none (by simp; omega)]
    simp

/-- The node's glue within the overhead term. -/
theorem glue_le (r m o ovh d : ℕ) (hr : 1 ≤ r) (hm : m ≤ r) (ho : 2 ≤ o) (hovh : 80 ≤ ovh)
    (hd : 2 * (o - d) ≤ o + 1) :
    r * ((59 * (o - d) + 87) * m + 66) + (90 * r + 71) * r + ((3 * (o + 1) + 23) * r + 28) * r +
        77 * m ≤ ovh * (r * (2 * r + m) * (o + 1)) := by
  generalize he : o - d = e at hd
  have h59 : 59 * e ≤ 30 * (o + 1) := by omega
  have hA : r * ((59 * e + 87) * m + 66) ≤ r * m * (30 * (o + 1)) + 87 * (r * m) + 66 * r := by
    have := Nat.mul_le_mul_right m h59
    nlinarith
  have hB : 80 * (r * (2 * r + m) * (o + 1)) ≤ ovh * (r * (2 * r + m) * (o + 1)) :=
    Nat.mul_le_mul_right _ hovh
  have hrm : m ≤ r * m := Nat.le_mul_of_pos_left m hr
  have hrr : r ≤ r * r := Nat.le_mul_of_pos_left r hr
  have hmr : r * m ≤ r * r := Nat.mul_le_mul_left r hm
  have ho1 : 3 ≤ o + 1 := by omega
  have hX : 3 * (r * m) ≤ r * m * (o + 1) := by nlinarith
  have hY : 3 * (r * r) ≤ r * r * (o + 1) := by nlinarith
  nlinarith

end

end LeanVM.Cost.Bounds.PMCore
