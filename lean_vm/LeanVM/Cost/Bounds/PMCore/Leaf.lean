module

public import LeanVM.Cost.Bounds.PMCore.LeafParts
public import LeanVM.Cost.Bounds.PMCore.Core
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic

public import LeanVM.Cost.Bounds.PMLane.InterpDefs
/-!
# Bounds: the PM-basis leaf at order one, compiled

The ordered-weak-Popov leaf (`popovLeafC`, `Popov.popovLeafBasis`) at order at most one on `n` rows
and `m` orders, and its compaction: the coefficient rows, the scalar kernel (`LeafKernel.lean`),
the kernel and completion rows reduced through the pivot table (`LeafReduce.lean`: the rank
potential, `O(n³)`), the slots filled. **`popovLeafC_cost`**: at most `leafBound n m`;
**`leafCost`**: the `LeafCost` the core's price (`Core.lean`) asks, at `leafBound r m`.
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Cost.Bounds.Decoder CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open LeanVM.Extraction.Fast.PMDegree (HomRowLe HomRow)

public section

theorem pivotPrice_mono {a b r : ℕ} (h : a ≤ b) : pivotPrice a r ≤ pivotPrice b r := by
  unfold pivotPrice; gcongr

theorem leafBound_mono (n : ℕ) {a b : ℕ} (h : a ≤ b) : leafBound n a ≤ leafBound n b := by
  have := pivotPrice_mono (r := n) h
  unfold leafBound; gcongr

theorem rowsInv_slot {n : ℕ} {shift : Array ℕ} {rows : PolynomialMatrix K} :
    ∀ p q, (LeanVM.Extraction.Fast.Popov.slotTable n shift rows).getD p none = some q → q ∈ rows.toList := by
  unfold LeanVM.Extraction.Fast.Popov.slotTable
  rw [← Array.foldl_toList]
  have key : ∀ (l : List (PolynomialRow K)) (T : Array (Option (PolynomialRow K))),
      (∀ p q, T.getD p none = some q → q ∈ rows.toList) → (∀ q ∈ l, q ∈ rows.toList) →
      ∀ p q, (l.foldl (LeanVM.Extraction.Fast.Popov.slotStep shift) T).getD p none = some q →
        q ∈ rows.toList := by
    intro l
    induction l with
    | nil => intro T hT _; exact hT
    | cons x l ih =>
      intro T hT hl
      apply ih _ _ (fun q hq ↦ hl q (by simp [hq]))
      intro p q hq
      simp only [LeanVM.Extraction.Fast.Popov.slotStep] at hq
      split at hq
      · rw [DenseMatrix.array_getD_setIfInBounds] at hq
        split_ifs at hq
        · cases hq; exact hl x (by simp)
        · exact hT p q hq
      · exact hT p q hq
  refine key _ _ (fun p q hq ↦ ?_) (fun q hq ↦ hq)
  rw [Array.getD_eq_getD_getElem?] at hq
  rcases Nat.lt_or_ge p n with hp | hp
  · rw [Array.getElem?_eq_getElem (by simpa using hp), Array.getElem_replicate] at hq; cases hq
  · rw [Array.getElem?_eq_none (by simpa using hp)] at hq; cases hq

variable (P : MachineProgram)

/-- The slot table (`slotTable`) of `R` rows of width `n`: at most `n + (191·n + 126)·R + 12`. -/
theorem slotTableC_cost
    (hP : Includes P Auto.LeanVM.Extraction.Fast.Popov.slotTable.c478.costDeps)
    {n S : ℕ} (hn : n < 2 ^ 30) (hS : S < 2 ^ 60) (shift : Array ℕ) (hs : ∀ j, shift.getD j 0 ≤ S)
    (rows : PolynomialMatrix K) (h : RowsInv n rows.toList) :
    machineCost P Auto.LeanVM.Extraction.Fast.Popov.slotTable.c478.costIdx
        [encodeValue n, encodeValue shift, encodeValue rows] ≤ n + (191 * n + 126) * rows.size + 12 := by
  rw [Auto.LeanVM.Extraction.Fast.Popov.slotTable.c478.costEq P hP]
  have hf := listFoldl_le P (by includes) (LeanVM.Extraction.Fast.Popov.slotStep shift)
    (.closure Auto.LeanVM.Extraction.Fast.Popov.slotTable.c478.lam0.costIdx [encodeValue shift])
    (fun a b ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.Fast.Popov.slotTable.c478.lam0.costSpec P
      (by includes) shift a b)) (191 * n + 114) (fun T ↦ T.size = n) rows.toList
    (Array.replicate n none) (by simp) (fun T hT row hrow ↦ ⟨by
      simp only [LeanVM.Extraction.Fast.Popov.slotStep]
      split <;> simp [hT], by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.LeanVM.Extraction.Fast.Popov.slotTable.c478.lam0.costEq P (by includes),
        Auto.LeanVM.Extraction.Fast.Popov.slotStep.c480.costEq P (by includes)]
      obtain ⟨hrs, hrh⟩ := h row hrow
      have := rowShiftedLeadingPosition_cost P (by includes) (C := n) (D := 2) (S := S) (by omega)
        (by omega) row (rowWithin_of_homRow hrs hrh) shift hs
      cases rowShiftedLeadingPosition? row shift <;> dsimp only <;> omega⟩)
  simp only [Array.length_toList] at hf
  nlinarith

/-- **The slots filled** (`fillPivotSlots`), `R ≤ n` rows. -/
theorem fillPivotSlotsC_cost
    (hP : Includes P Auto.LeanVM.Extraction.Fast.Popov.fillPivotSlots.c477.costDeps)
    (problem : XAdicProblem K) {S : ℕ} (hS : S < 2 ^ 60) (shift : Array ℕ)
    (hs : ∀ j, shift.getD j 0 ≤ S) (h1 : maxOrder problem ≤ 1) (hn : problem.matrix.size < 2 ^ 30)
    (hm : problem.orders.size < 2 ^ 30)
    (rows : PolynomialMatrix K) (h : RowsInv problem.matrix.size rows.toList)
    (hR : rows.size ≤ problem.matrix.size) :
    machineCost P Auto.LeanVM.Extraction.Fast.Popov.fillPivotSlots.c477.costIdx
        [encodeValue problem, encodeValue shift, encodeValue rows] ≤
      (problem.matrix.size + (191 * problem.matrix.size + 126) * problem.matrix.size + 12) +
        ((36 * problem.orders.size + 108 * problem.matrix.size + 75) * problem.matrix.size + 6) +
        problem.matrix.size + 18 := by
  rw [Auto.LeanVM.Extraction.Fast.Popov.fillPivotSlots.c477.costEq P hP]
  have hord : ∀ x ∈ problem.orders, x ≤ 1 := fun x hx ↦ (le_maxOrder problem x hx).trans h1
  have hcap : leafDegreeCap problem = 1 := LeanVM.Extraction.Fast.PMDegree.leafDegreeCap_eq_one h1
  have hst := slotTableC_cost P (by includes) hn hS shift hs rows h
  have : (191 * problem.matrix.size + 126) * rows.size ≤
      (191 * problem.matrix.size + 126) * problem.matrix.size := Nat.mul_le_mul_left _ hR
  have hof := ofFnFrom_cost P (by includes) (by omega : problem.matrix.size < 2 ^ 64) _
    (.closure Auto.LeanVM.Extraction.Fast.Popov.fillPivotSlots.c477.lam0.costIdx
      [encodeValue problem,
        encodeValue (LeanVM.Extraction.Fast.Popov.slotTable problem.matrix.size shift rows)])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.Fast.Popov.fillPivotSlots.c477.lam0.costSpec P
      (by includes) problem _ a)) (36 * problem.orders.size + 108 * problem.matrix.size + 57)
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.LeanVM.Extraction.Fast.Popov.fillPivotSlots.c477.lam0.costEq P (by includes)]
      have := leafDegreeCapC_cost P (by includes) problem (fun x hx ↦ by have := hord x hx; omega)
      have := monomialUnitRowC_cost P (by includes) problem.matrix.size i (leafDegreeCap problem)
        (by omega) (by have := i.isLt; omega) (by omega)
      have e2 : (25 * leafDegreeCap problem + 83) * problem.matrix.size = 108 * problem.matrix.size := by
        rw [hcap]
      cases (LeanVM.Extraction.Fast.Popov.slotTable problem.matrix.size shift rows).getD i none <;>
        dsimp only <;> omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length]
  simp only [Nat.sub_zero] at hof
  have e3 : (36 * problem.orders.size + 108 * problem.matrix.size + 57 + 18) * problem.matrix.size =
      (36 * problem.orders.size + 108 * problem.matrix.size + 75) * problem.matrix.size := by ring
  omega

theorem rowsInv_leafRows (problem : XAdicProblem K) (h1 : maxOrder problem ≤ 1) :
    RowsInv problem.matrix.size
      ((Array.map (vectorToPolynomialRow (leafDegreeCap problem) problem.matrix.size)
        (DenseMatrix.homogeneousKernelBasisRows (coefficientMatrixRows problem)
          (problem.matrix.size * leafDegreeCap problem))) ++ kernelLeafCompletionRows problem).toList := by
  have hcap : leafDegreeCap problem = 1 := LeanVM.Extraction.Fast.PMDegree.leafDegreeCap_eq_one h1
  intro q hq
  rw [Array.toList_append, List.mem_append] at hq
  rcases hq with hq | hq
  · simp only [Array.toList_map, List.mem_map] at hq
    obtain ⟨v, -, rfl⟩ := hq
    rw [hcap]
    exact ⟨by simp [vectorToPolynomialRow], 0, by omega,
      LeanVM.Extraction.Fast.PMDegree.homRow_vectorToPolynomialRow _ v⟩
  · simp only [kernelLeafCompletionRows, List.toList_toArray, List.mem_map, List.mem_range] at hq
    obtain ⟨i, -, rfl⟩ := hq
    rw [hcap]
    exact ⟨size_monomialUnitRow _ _ _, 1, le_rfl,
      LeanVM.Extraction.Fast.PMDegree.homRow_monomialUnitRow _ _ _⟩

/-- **The reduced kernel rows** (`kernelLeafReduced`) at order at most one: within the first part
of `leafBound`; at most `n` rows `X^e·v` of width `n`. -/
theorem kernelLeafReducedC_cost
    (hP : Includes P Auto.LeanVM.Extraction.Fast.Popov.kernelLeafReduced.c488.costDeps)
    (problem : XAdicProblem K) {S : ℕ} (hS : S < 2 ^ 60) (shift : Array ℕ)
    (hs : ∀ j, shift.getD j 0 ≤ S) (h1 : maxOrder problem ≤ 1) (hn : problem.matrix.size < 2 ^ 28)
    (hm : problem.orders.size < 2 ^ 28) :
    machineCost P Auto.LeanVM.Extraction.Fast.Popov.kernelLeafReduced.c488.costIdx
        [encodeValue problem, encodeValue shift] ≤
      (36 * problem.orders.size + 26) +
        (36 * problem.orders.size + 26 +
          (problem.orders.size * problem.orders.size + 160 * problem.orders.size + 64) +
          (69 * problem.matrix.size + 45) * problem.orders.size + 20) + 1 +
        ((problem.matrix.size + 1) * (42 * problem.orders.size + 80) +
          problem.orders.size * pivotPrice problem.orders.size problem.matrix.size +
          (33 * problem.matrix.size + 55) * problem.matrix.size * problem.matrix.size +
          (16 * problem.matrix.size + 90) * problem.matrix.size + 70) +
        3 * problem.matrix.size + ((129 * problem.matrix.size + 34) * problem.matrix.size + 3) +
        problem.matrix.size +
        (36 * problem.orders.size + ((25 + 83) * problem.matrix.size + 36) * problem.matrix.size +
          18 * problem.matrix.size + 50) + 2 * problem.matrix.size +
        (stepPrice problem.matrix.size * (2 * problem.matrix.size * (2 * problem.matrix.size)) +
          (incPrice problem.matrix.size + 16) * (2 * problem.matrix.size) + 11) + 28 ∧
      RowsInv problem.matrix.size (LeanVM.Extraction.Fast.Popov.kernelLeafReduced problem shift).toList ∧
      (LeanVM.Extraction.Fast.Popov.kernelLeafReduced problem shift).size ≤ problem.matrix.size := by
  have hord : ∀ x ∈ problem.orders, x ≤ 1 := fun x hx ↦ (le_maxOrder problem x hx).trans h1
  have hcap : leafDegreeCap problem = 1 := LeanVM.Extraction.Fast.PMDegree.leafDegreeCap_eq_one h1
  rw [Auto.LeanVM.Extraction.Fast.Popov.kernelLeafReduced.c488.costEq P hP]
  have hcl : (kernelLeafCompletionRows problem).size = problem.matrix.size := by
    simp [kernelLeafCompletionRows]
  set n := problem.matrix.size with hndef
  set mo := problem.orders.size with hmo
  have hord' : ∀ j, problem.orders.getD j 0 ≤ 1 := fun j ↦ getD_le_of_mem hord
  have hE := coefficientEquationIndices_size_le problem.orders hord'
  set E0 := (coefficientEquationIndices problem.orders).size with hE0
  have hldc := leafDegreeCapC_cost P (by includes) problem (fun x hx ↦ by have := hord x hx; omega)
  have hcr := coefficientMatrixRowsC_cost P (by includes) problem h1 (by omega) (by omega)
  have hshape := coefficientMatrixRows_shape problem
  rw [hcap, Nat.mul_one] at hshape
  have hkb := kernelBasisC_cost P (by includes) (E := E0) (r := n) (by omega) (by omega) n (by omega)
    (coefficientMatrixRows problem) hshape
  obtain ⟨-, -, hfree⟩ := rref_pivots (coefficientMatrixRows problem) n
  have hkbs : (DenseMatrix.homogeneousKernelBasisRows (coefficientMatrixRows problem) n).size ≤ n := by
    rw [DenseMatrix.homogeneousKernelBasisRows_size_eq]; exact hfree
  have hmap := map_cost P (by includes) (vectorToPolynomialRow 1 n)
    (.closure Auto.LeanVM.Extraction.Fast.Popov.kernelLeafReduced.c488.lam0.costIdx
      [encodeValue n, encodeValue 1])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.Fast.Popov.kernelLeafReduced.c488.lam0.costSpec P
      (by includes) n 1 a)) (129 * n + 23)
    (DenseMatrix.homogeneousKernelBasisRows (coefficientMatrixRows problem) n).toList (fun v _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.LeanVM.Extraction.Fast.Popov.kernelLeafReduced.c488.lam0.costEq P (by includes)]
      have := vectorToPolynomialRowC_cost P (by includes) 1 n v (by omega) (by omega)
      omega)
  have hcomp := completionRowsC_cost P (by includes) problem (fun x hx ↦ by have := hord x hx; omega)
    (by omega) (by rw [hcap]; omega)
  have hrows := rowsInv_leafRows problem h1
  have hred := reduceIncrementalC_cost P (by includes) (r := n) (S := S) (by omega) hS shift hs _ hrows
  have hrs : ((Array.map (vectorToPolynomialRow (leafDegreeCap problem) n)
      (DenseMatrix.homogeneousKernelBasisRows (coefficientMatrixRows problem) (n * leafDegreeCap problem))) ++
      kernelLeafCompletionRows problem).size ≤ 2 * n := by
    rw [Array.size_append, Array.size_map, hcap, Nat.mul_one]
    omega
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hr1, -, -⟩ := hred
    have e1 : stepPrice n * (2 * n * ((Array.map (vectorToPolynomialRow (leafDegreeCap problem) n)
        (DenseMatrix.homogeneousKernelBasisRows (coefficientMatrixRows problem) (n * leafDegreeCap problem))) ++
        kernelLeafCompletionRows problem).size) ≤ stepPrice n * (2 * n * (2 * n)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hrs)
    have e2 : (incPrice n + 16) * ((Array.map (vectorToPolynomialRow (leafDegreeCap problem) n)
        (DenseMatrix.homogeneousKernelBasisRows (coefficientMatrixRows problem) (n * leafDegreeCap problem))) ++
        kernelLeafCompletionRows problem).size ≤ (incPrice n + 16) * (2 * n) := Nat.mul_le_mul_left _ hrs
    have e3 : (n + 1) * (42 * E0 + 80) ≤ (n + 1) * (42 * mo + 80) := Nat.mul_le_mul_left _ (by omega)
    have e4 : E0 * pivotPrice E0 n ≤ mo * pivotPrice mo n :=
      Nat.mul_le_mul hE (pivotPrice_mono hE)
    have e5 : (129 * n + 23 + 11) *
        (DenseMatrix.homogeneousKernelBasisRows (coefficientMatrixRows problem) n).size ≤
        (129 * n + 34) * n := Nat.mul_le_mul_left _ hkbs
    simp only [Array.length_toList, List.length_map, Array.size_map] at hmap ⊢
    simp only [hcap, Nat.mul_one] at *
    simp only [← hndef, ← hmo] at *
    rw [limbs_of_lt (by omega : n < 2 ^ 64), limbs_of_lt (by norm_num : (1 : ℕ) < 2 ^ 64)]
    omega
  · exact hred.2.1
  · exact hred.2.2

/-- **The leaf at order at most one and its compaction**: at most `leafBound n m`. -/
theorem popovLeafC_cost (hP : Includes P pmCoreC.costDeps) (problem : XAdicProblem K) {S : ℕ}
    (hS : S < 2 ^ 60) (shift : Array ℕ) (hs : ∀ j, shift.getD j 0 ≤ S) (h1 : maxOrder problem ≤ 1)
    (hn : problem.matrix.size < 2 ^ 28) (hm : problem.orders.size < 2 ^ 28) :
    machineCost P popovLeafC.costIdx [encodeValue problem, encodeValue shift] +
        machineCost P compactNonzeroRowsC.costIdx
          [encodeValue (LeanVM.Extraction.Fast.Popov.popovLeafBasis problem shift)] ≤
      leafBound problem.matrix.size problem.orders.size := by
  rw [popovLeafC.costEq P (by includes)]
  obtain ⟨hk, hinv, hsz⟩ := kernelLeafReducedC_cost P (by includes) problem hS shift hs h1 hn hm
  have hf := fillPivotSlotsC_cost P (by includes) problem hS shift hs h1 (by omega) (by omega) _ hinv hsz
  have hcap : leafDegreeCap problem = 1 := LeanVM.Extraction.Fast.PMDegree.leafDegreeCap_eq_one h1
  have hrows : ∀ row ∈ (LeanVM.Extraction.Fast.Popov.popovLeafBasis problem shift).toList,
      RowWithin problem.matrix.size 2 row := by
    intro row hrow
    simp only [LeanVM.Extraction.Fast.Popov.popovLeafBasis, LeanVM.Extraction.Fast.Popov.fillPivotSlots,
      Array.toList_ofFn, List.mem_ofFn] at hrow
    obtain ⟨i, rfl⟩ := hrow
    cases hslot : (LeanVM.Extraction.Fast.Popov.slotTable problem.matrix.size shift
        (LeanVM.Extraction.Fast.Popov.kernelLeafReduced problem shift)).getD i none with
    | none => simp only [Option.getD_none]; rw [hcap]; exact rowWithin_monomialUnitRow _ _
    | some q =>
      simp only [Option.getD_some]
      obtain ⟨hqs, hqh⟩ := hinv q (rowsInv_slot _ _ hslot)
      exact rowWithin_of_homRow hqs hqh
  have hc := compactNonzeroRowsC_cost P (by includes) (C := problem.matrix.size) (D := 2)
    (LeanVM.Extraction.Fast.Popov.popovLeafBasis problem shift) hrows
  have hps : (LeanVM.Extraction.Fast.Popov.popovLeafBasis problem shift).size = problem.matrix.size := by
    simp [LeanVM.Extraction.Fast.Popov.popovLeafBasis, LeanVM.Extraction.Fast.Popov.fillPivotSlots]
  rw [hps] at hc
  have e : LeanVM.Extraction.Fast.Popov.popovLeafBasis problem shift =
      LeanVM.Extraction.Fast.Popov.fillPivotSlots problem shift
        (LeanVM.Extraction.Fast.Popov.kernelLeafReduced problem shift) := rfl
  have e1 : ((3 * 2 + 23) * problem.matrix.size + 28) * problem.matrix.size =
      (29 * problem.matrix.size + 28) * problem.matrix.size := by norm_num
  unfold leafBound
  omega

/-- **The leaf's price as the core asks it** (`LeafCost`, `Core.lean`): at `leafBound r m`. -/
theorem leafCost (hP : Includes P pmCoreC.costDeps) {r m SB : ℕ} (hr : r < 2 ^ 28)
    (hm : m < 2 ^ 28) (hSB : SB < 2 ^ 39) : LeafCost P r m SB (leafBound r m) := by
  intro problem shift hI h1
  obtain ⟨hIs, -, hIo, -, hIsh, -⟩ := hI
  have := popovLeafC_cost P hP problem (S := SB) (by omega) shift (fun j ↦ by have := hIsh j; omega)
    h1 (by omega) (by omega)
  rw [hIs] at this
  exact this.trans (leafBound_mono r hIo)

end

end LeanVM.Cost.Bounds.PMCore
