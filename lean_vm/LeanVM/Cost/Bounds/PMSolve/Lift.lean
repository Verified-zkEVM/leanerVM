module

public import LeanVM.Cost.Bounds.PMSolve.Small
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Operations
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation.Basic

/-!
# Bounds: the certified problem's lift, compiled

`fullWindowExactNullspaceProblem fftModContext equation bound` (`fullWindowProblemC`): the orders
`deg M_b + bound + 2`, and the lift `reducedExactNullspaceLift`: each relation entry reduced modulo
its column's modulus, then `−diag(M)`. On the Guruswami–Sudan data the entries are reduced already
(`natDegree_gsRelationMatrix_entry_lt`, `Fast/PMShape.lean`), so each remainder takes the reversal
remainder's first branch: its guard reads both operands (`modByMonicFFTC_first_cost`, `≤ 41·|p| +
64·|q| + 130`), no product. `ofFnC_cost`: CompPoly's `ofFn` of a priced entry.

**`fullWindowProblemC_cost`**: on `w` relation rows, `m` monic moduli of at most `Q` coefficients,
entries shorter than their column's modulus: at most `liftPrice Q w m`.
-/

namespace LeanVM.Cost.Bounds.PMSolve

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

open LeanVM.Cost.Auto.CompPoly.PolynomialMatrix.Approximant LeanVM.Cost.Auto.CompPoly.PolynomialMatrix

public section

variable (P : MachineProgram)

/-- **CompPoly's `ofFn`** of an entry of price at most `B`: at most
`rows·(width·(B + 33) + 48) + 19`. -/
theorem ofFnC_cost (hP : Includes P ofFn.c920.costDeps) (rows width : ℕ) (hr : rows < 2 ^ 62)
    (hw : width < 2 ^ 62) (entry : ℕ → ℕ → CPolynomial K) (eVal : MachineValue)
    (he : ∀ a b, RunsApp P eVal [encodeValue a, encodeValue b] (encodeValue (entry a b))) (B : ℕ)
    (hB : ∀ i < rows, ∀ j < width, appCost P eVal [encodeValue i, encodeValue j] ≤ B) :
    machineCost P ofFn.c920.costIdx [encodeValue rows, encodeValue width, eVal] ≤
      rows * (width * (B + 33) + 48) + 19 := by
  rw [ofFn.c920.costEq P hP rows width entry eVal he]
  have := rangeLoop_cost P (by includes) rows [] (by omega)
  have hl := fun i ↦ RunsApp.of_spec (us := [encodeValue width, eVal]) (vs := [encodeValue i])
    (ofFn.c920.lam0.costSpec P (by includes) width entry eVal he i)
  have := map_cost P (by includes) _ (.closure ofFn.c920.lam0.costIdx [encodeValue width, eVal])
    hl (width * (B + 33) + 19) (List.range rows) (fun i hi ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [ofFn.c920.lam0.costEq P (by includes) width entry eVal he i]
      have := rangeLoop_cost P (by includes) width [] (by omega)
      have hl2 := fun j ↦ RunsApp.of_spec (us := [eVal, encodeValue i]) (vs := [encodeValue j])
        (ofFn.c920.lam0.lam0.costSpec P (by includes) entry eVal he i j)
      have := map_cost P (by includes) _ (.closure ofFn.c920.lam0.lam0.costIdx [eVal, encodeValue i])
        hl2 (B + 4) (List.range width) (fun j hj ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append]
          rw [ofFn.c920.lam0.lam0.costEq P (by includes) entry eVal he i j]
          have := hB i (List.mem_range.1 hi) j (List.mem_range.1 hj)
          omega)
      simp only [List.length_range, List.length_map] at *
      have e : width * (B + 33) = (B + 4 + 11) * width + 18 * width := by ring
      omega)
  simp only [List.length_range, List.length_map] at *
  have e : rows * (width * (B + 33) + 48) = (width * (B + 33) + 19 + 11) * rows + 18 * rows := by
    ring
  omega

theorem cpoly_trim_eq (p : CPolynomial K) : p.val.trim = p.val :=
  CPolynomial.Raw.Trim.trim_eq_of_isCanonical p.property

/-- **The reversal remainder's first branch** (`modByMonicFFTC`, the dividend shorter than the
monic modulus): the guard reads both, at most `41·|p| + 64·|q| + 130`. -/
theorem modByMonicFFTC_first_cost (hP : Includes P modByMonicFFTC.costDeps) (p q : CPolynomial K)
    (hq : q.monic = true) (hpq : p.val.size < q.val.size) (hqs : q.val.size < 2 ^ 60) :
    machineCost P modByMonicFFTC.costIdx [encodeValue p, encodeValue q] ≤
      41 * p.val.size + 64 * q.val.size + 130 := by
  rw [modByMonicFFTC.costEq P hP, Auto.CompPoly.CPolynomial.Raw.modByMonicByReversal.c905.costEq P
    (by includes)]
  have hpt := cpoly_trim_eq p
  have hqt := cpoly_trim_eq q
  have hlc : (CPolynomial.Raw.leadingCoeff q.val == 1) = true := by
    simpa [CPolynomial.monic, CPolynomial.leadingCoeff, CPolynomial.Raw.leadingCoeff, hqt] using hq
  have := trimLen_cost P (by includes) p.val p.val.size (by omega)
  have := trimLen_cost P (by includes) q.val q.val.size (by omega)
  have := listBeqK_cost P (by includes) p.val.toList p.val.toList
  have := listBeqK_cost P (by includes) q.val.toList q.val.toList
  have := getLastDC_cost P (by includes) q.val 0 (by omega)
  have h1 : (Array.extract p.val 0 (CompPolyLib.trimLen p.val p.val.size)).size ≤ p.val.size := by
    simp
  have h2 : (Array.extract q.val 0 (CompPolyLib.trimLen q.val q.val.size)).size ≤ q.val.size := by
    simp
  have hp64 : p.val.size < 2 ^ 64 := by omega
  have hq64 : q.val.size < 2 ^ 64 := by omega
  simp only [hpt, hqt, beq_self_eq_true, Bool.true_and, hlc, ↓reduceIte, hpq, Array.length_toList]
    at *
  rw [limbs_of_lt hp64, limbs_of_lt hq64]
  omega

/-- The lift's entry (`reducedExactNullspaceLift.c1032.lam0`): an entry read and reduced on the
first branch, at most `120·Q + 170` for moduli of at most `Q` coefficients. -/
theorem liftEntryC_cost (hP : Includes P reducedExactNullspaceLift.c1032.lam0.costDeps)
    (equation : ModularEquation K) (i j : ℕ) {Q : ℕ} (hQ : Q < 2 ^ 60)
    (hq : (equation.moduli.getD j 0).monic = true)
    (hqQ : (equation.moduli.getD j 0).val.size ≤ Q)
    (hred : (rowGet (equation.matrix.getD i #[]) j).val.size <
      (equation.moduli.getD j 0).val.size) :
    machineCost P reducedExactNullspaceLift.c1032.lam0.costIdx
        [encodeValue equation, encodeValue i, encodeValue j] ≤ 120 * Q + 170 := by
  rw [reducedExactNullspaceLift.c1032.lam0.costEq P hP, modByMonicWith.c1034.costEq P (by includes)]
  have := rowGet_cost P (by includes) (equation.matrix.getD i #[]) j
  have := listBeqK_cost P (by includes) (equation.moduli.getD j 0).val.toList
    (↑(0 : CPolynomial K) : Array K).toList
  have := modByMonicFFTC_first_cost P (by includes) _ _ hq hred (by omega)
  have hz : (↑(0 : CPolynomial K) : Array K).size = 0 := rfl
  simp only [Array.length_toList, hz] at *
  split <;> omega

/-- `−diag(M)`'s entry: at most `16·Q + 20`. -/
theorem negDiagEntryC_cost (hP : Includes P negativeDiagonalRows.c1036.lam0.costDeps)
    (moduli : Array (CPolynomial K)) (i j : ℕ) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) {Q : ℕ}
    (hqQ : (moduli.getD i 0).val.size ≤ Q) :
    machineCost P negativeDiagonalRows.c1036.lam0.costIdx
        [encodeValue moduli, encodeValue i, encodeValue j] ≤ 16 * Q + 20 := by
  rw [negativeDiagonalRows.c1036.lam0.costEq P hP]
  have hl := fun a ↦ RunsApp.of_spec (us := []) (vs := [encodeValue a])
    (Auto.CompPoly.CPolynomial.Raw.sub.c152.lam0.costSpec P (by includes) a)
  have := map_cost P (by includes) _ (.closure Auto.CompPoly.CPolynomial.Raw.sub.c152.lam0.costIdx [])
    hl 1 (↑(moduli.getD i 0) : Array K).toList (fun a _ ↦ by
      simp only [appCost_fn, List.nil_append]
      rw [Auto.CompPoly.CPolynomial.Raw.sub.c152.lam0.costEq P (by includes)])
  simp only [Array.length_toList, List.length_map] at *
  cost_simp
  split <;> omega


/-- The lift's price: `w·m` entries reduced on the first branch, `−diag(M)`, the orders. -/
@[expose] def liftPrice (Q w m : ℕ) : ℕ :=
  w * (m * (120 * Q + 203) + 48) + m * (m * (16 * Q + 53) + 48) + w + 40 * m + 90

/-- The sizes the lift's price reads: `w` relation rows, `m` monic moduli of at most `Q`
coefficients, each entry shorter than its column's modulus. -/
@[expose] def LiftSizes (equation : ModularEquation K) (w m Q : ℕ) : Prop :=
  equation.matrix.size = w ∧ equation.moduli.size = m ∧ w < 2 ^ 29 ∧ m < 2 ^ 29 ∧ Q < 2 ^ 60 ∧
    (∀ j < m, (equation.moduli.getD j 0).monic = true ∧ (equation.moduli.getD j 0).val.size ≤ Q) ∧
    ∀ i < w, ∀ j < m, (rowGet (equation.matrix.getD i #[]) j).val.size <
      (equation.moduli.getD j 0).val.size

theorem ofFn_size_eq (rows width : ℕ) (e : ℕ → ℕ → CPolynomial K) :
    (PolynomialMatrix.ofFn rows width e).size = rows := by
  simp [PolynomialMatrix.ofFn]

/-- **The lift** (`reducedExactNullspaceLift`): at most
`w·(m·(120·Q + 203) + 48) + m·(m·(16·Q + 53) + 48) + w + m + 70`. -/
theorem reducedLiftC_cost (hP : Includes P reducedExactNullspaceLift.c1032.costDeps)
    (equation : ModularEquation K) {w m Q : ℕ} (hs : LiftSizes equation w m Q) :
    machineCost P reducedExactNullspaceLift.c1032.costIdx [encodeValue equation] ≤
      w * (m * (120 * Q + 203) + 48) + m * (m * (16 * Q + 53) + 48) + w + m + 70 := by
  obtain ⟨hw, hm, hw30, hm30, hQ, hmod, hred⟩ := hs
  rw [reducedExactNullspaceLift.c1032.costEq P hP,
    ModularEquation.solutionWidth.c1024.costEq P (by includes),
    ModularEquation.modularWidth.c1035.costEq P (by includes),
    negativeDiagonalRows.c1036.costEq P (by includes)]
  have hsW : equation.solutionWidth = w := hw
  have hmW : equation.modularWidth = m := hm
  have he1 := fun i j ↦ RunsApp.of_spec (us := [encodeValue equation])
    (vs := [encodeValue i, encodeValue j])
    (reducedExactNullspaceLift.c1032.lam0.costSpec P (by includes) equation i j)
  have h1 := ofFnC_cost P (by includes) equation.solutionWidth equation.modularWidth
    (by omega) (by omega) _ (.closure reducedExactNullspaceLift.c1032.lam0.costIdx
      [encodeValue equation]) he1 (120 * Q + 170) (fun i hi j hj ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [hsW] at hi
      rw [hmW] at hj
      exact liftEntryC_cost P (by includes) equation i j (by omega) (hmod j hj).1 (hmod j hj).2
        (hred i hi j hj))
  have he2 := fun i j ↦ RunsApp.of_spec (us := [encodeValue equation.moduli])
    (vs := [encodeValue i, encodeValue j])
    (negativeDiagonalRows.c1036.lam0.costSpec P (by includes) equation.moduli i j)
  have h2 := ofFnC_cost P (by includes) equation.moduli.size equation.moduli.size
    (by omega) (by omega) _ (.closure negativeDiagonalRows.c1036.lam0.costIdx
      [encodeValue equation.moduli]) he2 (16 * Q + 20) (fun i hi j hj ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      exact negDiagEntryC_cost P (by includes) equation.moduli i j (by omega) (by omega)
        (hmod i (by omega)).2)
  simp only [hsW, hmW] at h1 ⊢
  simp only [hm] at h2 ⊢
  have hz1 := ofFn_size_eq equation.solutionWidth equation.modularWidth
    (fun i j ↦ modByMonicWith FFT.fftModContext (rowGet (equation.matrix.getD i #[]) j)
      (equation.moduli.getD j 0))
  have hz2 : (negativeDiagonalRows equation.moduli).size = equation.moduli.size :=
    ofFn_size_eq _ _ _
  rw [hsW, hmW] at hz1
  rw [hm] at hz2
  rw [hz1, hz2]
  have e1 : w * (m * (120 * Q + 170 + 33) + 48) = w * (m * (120 * Q + 203) + 48) := by ring
  have e2 : m * (m * (16 * Q + 20 + 33) + 48) = m * (m * (16 * Q + 53) + 48) := by ring
  omega

/-- **The certified problem** (`fullWindowExactNullspaceProblem fftModContext`): the orders and
the lift, at most `liftPrice Q w m`. -/
theorem fullWindowProblemC_cost (hP : Includes P fullWindowProblemC.costDeps)
    (equation : ModularEquation K) (bound : ℕ) (hb : bound < 2 ^ 62) {w m Q : ℕ}
    (hs : LiftSizes equation w m Q) :
    machineCost P fullWindowProblemC.costIdx [encodeValue equation, encodeValue bound] ≤
      liftPrice Q w m := by
  have hs' := hs
  obtain ⟨hw, hm, hw30, hm30, hQ, hmod, hred⟩ := hs'
  rw [fullWindowProblemC.costEq P hP]
  have := reducedLiftC_cost P (by includes) equation hs
  have hl := fun M ↦ RunsApp.of_spec (us := [encodeValue bound]) (vs := [encodeValue M])
    (fullWindowProblemC.lam0.costSpec P (by includes) bound M)
  have := map_cost P (by includes) _ (.closure fullWindowProblemC.lam0.costIdx [encodeValue bound])
    hl 21 equation.moduli.toList (fun M hM ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [fullWindowProblemC.lam0.costEq P (by includes)]
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hM
      have hj' : j < m := by simpa [hm] using hj
      have hsz := (hmod j hj').2
      have hget : equation.moduli.getD j 0 = equation.moduli.toList[j] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hj)]
        simp
      rw [hget] at hsz
      have := natDegree_cost P (by includes) equation.moduli.toList[j] (by omega)
      have := natDegree_le_size equation.moduli.toList[j]
      cost_simp
      omega)
  simp only [Array.length_toList, List.length_map] at *
  unfold liftPrice
  rw [hm]
  omega

end

end LeanVM.Cost.Bounds.PMSolve
