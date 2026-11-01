module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Samples.MsStep
import all CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann
import all CompPoly.LinearAlgebra.PolynomialMatrix.Shifted
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic

/-!
# Bound: one Mulders–Storjohann step over `K`

The price of the compiled step (`Cost/Samples/MsStep.lean`, `muldersStorjohannStepFast`; its
callees are the extractor's, `Cost/Extractor/MsReduce.lean`, so these bounds serve both):
`msStep_cost`, at most `|M| + 740·D·C + 970·C + 30·D + 21100` for rows of at most `C` entries of
at most `D` coefficients (`RowWithin`) and shifts at most `S`, word-sized (`2·D + S < 2^62`,
`C < 2^62`). Bottom up:

* an entry's shifted degree (a constant: its zero test reads its size, `shiftedEntryDegree?_eq`,
  `Cost/Extractor/Rewrites.lean`), a row's (`rowShiftedDegree_cost`, a fold over the row:
  `90·C + 30`), its leading position (a `find?` over the reversed indices: `190·C + 100`) and
  leading term (`280·C + 15·D + 250`);
* a field inverse (`invK_cost`: `19700`; `powTwoPow_cost` exact, `6 + 270·k`);
* the subtraction `a − c·X^d·b` (`subMulMonomialEntry_cost`, per entry `370·(D + d) + 200`;
  `rowSubScaledShift_cost`);
* the cancellation and the step.

The values the step computes enter its price through `limbCount` (degrees, positions) and through
the lengths it iterates over: `shiftedEntryDegree?_le`, `rowShiftedDegree?_le` and
`rowShiftedLeadingTerm?_spec` bound them (the degrees by `D + S`, the position by the row's size,
the leading degree by `D`). Products of sizes are stated with `D·C` as one atom
(`affine_mul_le`), so that sums of bounds stay linear for `omega`.
-/

namespace LeanVM.Cost.Bounds.Samples

open LeanVM.Cost LeanVM.Cost.Samples LeanVM.Cost.Library LeanVM.Cost.Bounds LeanVM.Parameters
open CompPoly CompPoly.PolynomialMatrix

/-! The functions compiled on demand, by their short names (`rowGet.c17`: `Auto.…rowGet.c17`). -/
open LeanVM.Cost.Auto.CompPoly.PolynomialMatrix

public section

/-! ## The data: rows of at most `C` entries of at most `D` coefficients -/

/-- A row of at most `C` entries, each of at most `D` coefficients. -/
@[expose] def RowWithin (C D : ℕ) (row : PolynomialRow K) : Prop :=
  row.size ≤ C ∧ ∀ e ∈ row, e.val.size ≤ D

theorem RowWithin.size_rowGet {C D : ℕ} {row : PolynomialRow K} (h : RowWithin C D row) (j : ℕ) :
    (rowGet row j).val.size ≤ D := by
  unfold rowGet
  rw [Array.getD_eq_getD_getElem?]
  cases hj : row[j]? with
  | none => exact Nat.zero_le D
  | some e => exact h.2 e (Array.mem_of_getElem? hj)

theorem RowWithin.empty (C D : ℕ) : RowWithin C D #[] := ⟨by simp, by simp⟩

theorem natDegree_le_size (p : CPolynomial K) : p.natDegree ≤ p.val.size := by
  unfold CPolynomial.natDegree
  split <;> omega

theorem size_zero_val : (↑(0 : CPolynomial K) : Array K).size = 0 := rfl

theorem toList_zero_val : (↑(0 : CPolynomial K) : Array K).toList = [] := rfl

theorem shiftedEntryDegree?_le {C D S : ℕ} {row : PolynomialRow K} (h : RowWithin C D row)
    {shift : Array ℕ} (hS : ∀ j, shift.getD j 0 ≤ S) {j v : ℕ}
    (hv : shiftedEntryDegree? row shift j = some v) : v ≤ D + S := by
  unfold shiftedEntryDegree? at hv
  by_cases hz : (rowGet row j == 0) = true
  · simp [hz] at hv
  · simp only [hz, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hv
    have := natDegree_le_size (rowGet row j)
    have := h.size_rowGet j
    have := hS j
    omega

variable (P : MachineProgram)

/-! ## The shifted degree of a row -/

theorem rowGet_cost (hP : Includes P rowGet.c17.costDeps)
    (row : PolynomialRow K) (j : ℕ) :
    machineCost P rowGet.c17.costIdx [encodeValue row, encodeValue j] = 5 := by
  rw [rowGet.c17.costEq P hP]

/-- `List.beq` on coefficients: at most `12` per coefficient and `7`. -/
theorem listBeqK_cost (hP : Includes P Auto.List.beq.c27.costDeps) :
    ∀ a b : List K, machineCost P Auto.List.beq.c27.costIdx [encodeValue a, encodeValue b] ≤ 12 * a.length + 7 := by
  intro a
  induction a with
  | nil => intro b; rw [Auto.List.beq.c27.costEq P hP]; cases b <;> simp
  | cons x a ih =>
    intro b
    rw [Auto.List.beq.c27.costEq P hP]
    cases b with
    | nil => simp
    | cons y b =>
      have := ih b
      simp only [List.length_cons]
      split_ifs <;> omega

theorem natDegree_cost (hP : Includes P Auto.CompPoly.CPolynomial.natDegree.c18.costDeps)
    (p : CPolynomial K) (hp : p.val.size < 2 ^ 64) :
      machineCost P Auto.CompPoly.CPolynomial.natDegree.c18.costIdx [encodeValue p] ≤ 13 := by
  rw [Auto.CompPoly.CPolynomial.natDegree.c18.costEq P hP]
  have hp' := hp
  cases h : p.val.size with
  | zero => cost_simp; omega
  | succ k => cost_simp; omega

theorem maxOption_cost (hP : Includes P maxOption.c19.costDeps)
    (a : Option ℕ) (n : ℕ) (ha : ∀ v, a = some v → v < 2 ^ 64) (hn : n < 2 ^ 64) :
    machineCost P maxOption.c19.costIdx [encodeValue a, encodeValue n] ≤ 10 := by
  rw [maxOption.c19.costEq P hP]
  cases a with
  | none => simp
  | some v => have := ha v rfl; cost_simp; split_ifs <;> omega

/-- `List.range`'s loop: at most `17·n + 6`. -/
theorem rangeLoop_cost (hP : Includes P Auto.List.range.loop.c20.costDeps) :
    ∀ (n : ℕ) (acc : List ℕ), n < 2 ^ 64 →
      machineCost P Auto.List.range.loop.c20.costIdx [encodeValue n, encodeValue acc] ≤ 17 * n + 6 := by
  intro n
  induction n with
  | zero => intro acc _; rw [Auto.List.range.loop.c20.costEq P hP]; cost_simp; omega
  | succ k ih =>
    intro acc hk
    rw [Auto.List.range.loop.c20.costEq P hP]
    have := ih (k :: acc) (by omega)
    cost_simp
    omega

/-- The fold's step of the shifted degree: an invariant of word-sized maxima. -/
theorem foldl_shiftedDegree_le {C D S : ℕ} {row : PolynomialRow K} (h : RowWithin C D row)
    {shift : Array ℕ} (hS : ∀ j, shift.getD j 0 ≤ S) :
    ∀ (l : List ℕ) (acc : Option ℕ), (∀ v, acc = some v → v ≤ D + S) →
      ∀ v, l.foldl (fun acc j ↦ match shiftedEntryDegree? row shift j with
        | none => acc
        | some d => maxOption acc d) acc = some v → v ≤ D + S := by
  intro l
  induction l with
  | nil => intro acc hacc v hv; exact hacc v hv
  | cons j l ih =>
    intro acc hacc
    apply ih
    intro v hv
    dsimp only at hv
    generalize he : shiftedEntryDegree? row shift j = o at hv
    cases o with
    | none => exact hacc v hv
    | some d =>
      have hd := shiftedEntryDegree?_le h hS he
      cases acc with
      | none => simp only [maxOption, Option.some.injEq] at hv; omega
      | some m =>
        have := hacc m rfl
        simp only [maxOption, Option.some.injEq] at hv
        omega

theorem rowShiftedDegree?_le {C D S : ℕ} {row : PolynomialRow K} (h : RowWithin C D row)
    {shift : Array ℕ} (hS : ∀ j, shift.getD j 0 ≤ S) {v : ℕ}
    (hv : rowShiftedDegree? row shift = some v) : v ≤ D + S :=
  foldl_shiftedDegree_le h hS _ none (by simp) v hv

/-- **The shifted degree of a row** (`rowShiftedDegree?`): at most `90·C + 30` (an entry's shifted
degree costs a constant: its zero test reads the entry's size, `shiftedEntryDegree?_eq`). -/
theorem rowShiftedDegree_cost
    (hP : Includes P rowShiftedDegree?.c15.costDeps)
    {C D S : ℕ} (hC : C < 2 ^ 62) (hDS : D + S < 2 ^ 62) (row : PolynomialRow K)
    (hrow : RowWithin C D row) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P rowShiftedDegree?.c15.costIdx [encodeValue row, encodeValue shift] ≤ 90 * C + 30 := by
  rw [rowShiftedDegree?.c15.costEq P hP]
  have hsz := hrow.1
  have := rangeLoop_cost P (by includes) row.size [] (by omega)
  have hfold :=
    listFoldl_le P (by includes) _ (.closure rowShiftedDegree?.c15.lam0.costIdx [encodeValue row, encodeValue shift])
    (fun acc j ↦ RunsApp.of_spec
      (rowShiftedDegree?.c15.lam0.costSpec P (by includes)
        row shift acc j))
    60 (fun acc ↦ ∀ v, acc = some v → v ≤ D + S) (List.range row.size) none
    (by simp)
    (fun acc hacc j _ ↦ by
      refine ⟨?_, ?_⟩
      · intro v hv
        generalize he : shiftedEntryDegree? row shift j = o at hv
        cases o with
        | none => exact hacc v hv
        | some d =>
          have hd := shiftedEntryDegree?_le hrow hS he
          cases acc with
          | none => simp only [maxOption, Option.some.injEq] at hv; omega
          | some m =>
            have := hacc m rfl
            simp only [maxOption, Option.some.injEq] at hv
            omega
      · rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
          rowShiftedDegree?.c15.lam0.costEq P (by includes)]
        have := rowGet_cost P (by includes) row j
        have := hrow.size_rowGet j
        have := natDegree_cost P (by includes) (rowGet row j) (by omega)
        have := natDegree_le_size (rowGet row j)
        have := hS j
        generalize he : shiftedEntryDegree? row shift j = o
        cases o with
        | none => dsimp only; cost_simp; split_ifs <;> omega
        | some d =>
          have := shiftedEntryDegree?_le hrow hS he
          have := maxOption_cost P (by includes) acc d (fun v hv ↦ by have := hacc v hv; omega)
            (by omega)
          dsimp only
          cost_simp
          split_ifs <;> omega)
  simp only [List.length_range] at hfold
  cost_simp
  omega

/-! ## The shifted leading term of a row -/

/-- `List.find?` on indices: `9` per index and the predicate's price, `3` at the end. -/
theorem findNat_cost (hP : Includes P Auto.List.find?.c21.costDeps) (p : ℕ → Bool) (pVal : MachineValue)
    (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : ℕ) :
    ∀ l : List ℕ, (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B) →
      machineCost P Auto.List.find?.c21.costIdx [pVal, encodeValue l] ≤ (B + 9) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.find?.c21.costEq P hP p pVal hp]; simp
  | cons x l ih =>
    intro hB
    rw [Auto.List.find?.c21.costEq P hP p pVal hp]
    have h1 := ih fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons]
    generalize p x = b
    cases b <;> dsimp only <;> nlinarith

/-- `List.reverseAux` on indices: `10` per index, `3` at the end. -/
theorem reverseAuxNat_cost (hP : Includes P Auto.List.reverseAux.c23.costDeps) :
    ∀ l acc : List ℕ, machineCost P Auto.List.reverseAux.c23.costIdx [encodeValue l, encodeValue acc] ≤
      10 * l.length + 3 := by
  intro l
  induction l with
  | nil => intro acc; rw [Auto.List.reverseAux.c23.costEq P hP]; simp
  | cons x l ih =>
    intro acc
    rw [Auto.List.reverseAux.c23.costEq P hP]
    have := ih (x :: acc)
    simp only [List.length_cons]
    omega

/-- The leading position's test at one index: at most `60`. -/
theorem leadingPositionTest_cost
    (hP : Includes P rowShiftedLeadingPosition?.c14.lam0.costDeps)
    {C D S : ℕ} (hDS : D + S < 2 ^ 62) (val : ℕ) (hval : val ≤ D + S) (row : PolynomialRow K)
    (hrow : RowWithin C D row) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) (j : ℕ) :
    machineCost P rowShiftedLeadingPosition?.c14.lam0.costIdx [encodeValue val, encodeValue row, encodeValue shift, encodeValue j] ≤
      60 := by
  rw [rowShiftedLeadingPosition?.c14.lam0.costEq P hP]
  have := rowGet_cost P (by includes) row j
  have := hrow.size_rowGet j
  have := natDegree_cost P (by includes) (rowGet row j) (by omega)
  have := natDegree_le_size (rowGet row j)
  have := hS j
  generalize he : shiftedEntryDegree? row shift j = o
  cases o with
  | none => dsimp only; cost_simp; split_ifs <;> omega
  | some d =>
    have := shiftedEntryDegree?_le hrow hS he
    dsimp only
    cost_simp
    split_ifs <;> omega

/-- **The shifted leading position of a row**: at most `190·C + 100`. -/
theorem rowShiftedLeadingPosition_cost
    (hP : Includes P rowShiftedLeadingPosition?.c14.costDeps)
    {C D S : ℕ} (hC : C < 2 ^ 62) (hDS : D + S < 2 ^ 62) (row : PolynomialRow K)
    (hrow : RowWithin C D row) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P rowShiftedLeadingPosition?.c14.costIdx [encodeValue row, encodeValue shift] ≤
      190 * C + 100 := by
  rw [rowShiftedLeadingPosition?.c14.costEq P hP]
  have hsz := hrow.1
  have := rowShiftedDegree_cost P (by includes) hC hDS row hrow shift hS
  generalize he : rowShiftedDegree? row shift = o
  cases o with
  | none => dsimp only; omega
  | some val =>
    have hval := rowShiftedDegree?_le hrow hS he
    have := rangeLoop_cost P (by includes) row.size [] (by omega)
    have := reverseAuxNat_cost P (by includes) (List.range row.size) []
    have hf :=
      findNat_cost P (by includes) _
        (.closure rowShiftedLeadingPosition?.c14.lam0.costIdx [encodeValue val, encodeValue row, encodeValue shift])
      (fun a ↦ RunsApp.of_spec
        (rowShiftedLeadingPosition?.c14.lam0.costSpec P
          (by includes) val row shift a)) 60 (List.range row.size).reverse
      (fun a _ ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
        exact leadingPositionTest_cost P (by includes) hDS val hval row hrow shift hS a)
    simp only [List.length_reverse, List.length_range] at hf this
    dsimp only
    cost_simp
    omega

theorem rowShiftedLeadingPosition?_lt {row : PolynomialRow K} {shift : Array ℕ} {j : ℕ}
    (h : rowShiftedLeadingPosition? row shift = some j) : j < row.size := by
  unfold rowShiftedLeadingPosition? at h
  split at h
  · simp at h
  · have := List.mem_of_find?_eq_some h
    simpa using this

/-- The shifted leading term of a row of the bounds: its position in the row, its degree at
most `D`. -/
theorem rowShiftedLeadingTerm?_spec {C D : ℕ} {row : PolynomialRow K} (hrow : RowWithin C D row)
    {shift : Array ℕ} {t : ShiftedLeadingTerm K} (h : rowShiftedLeadingTerm? row shift = some t) :
    t.position < row.size ∧ t.degree ≤ D := by
  unfold rowShiftedLeadingTerm? at h
  split at h
  · rename_i j hd hj
    by_cases hz : (rowGet row j == 0) = true
    · simp [hz] at h
    · simp only [hz, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      have := natDegree_le_size (rowGet row j)
      have := hrow.size_rowGet j
      exact ⟨rowShiftedLeadingPosition?_lt hj, by dsimp only; omega⟩
  · simp at h

/-- **The shifted leading term of a row**: at most `280·C + 15·D + 250`. -/
theorem rowShiftedLeadingTerm_cost
    (hP : Includes P rowShiftedLeadingTerm?.c26.costDeps)
    {C D S : ℕ} (hC : C < 2 ^ 62) (hDS : D + S < 2 ^ 62) (row : PolynomialRow K)
    (hrow : RowWithin C D row) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P rowShiftedLeadingTerm?.c26.costIdx [encodeValue row, encodeValue shift] ≤
      280 * C + 15 * D + 250 := by
  rw [rowShiftedLeadingTerm?.c26.costEq P hP]
  have := rowShiftedDegree_cost P (by includes) hC hDS row hrow shift hS
  have := rowShiftedLeadingPosition_cost P (by includes) hC hDS row hrow shift hS
  generalize rowShiftedDegree? row shift = o
  cases o with
  | none => dsimp only; omega
  | some val =>
    generalize rowShiftedLeadingPosition? row shift = o'
    cases o' with
    | none => dsimp only; omega
    | some j =>
      have := rowGet_cost P (by includes) row j
      have hs := hrow.size_rowGet j
      have := listBeqK_cost P (by includes) (rowGet row j).val.toList
        (↑(0 : CPolynomial K) : Array K).toList
      have := natDegree_cost P (by includes) (rowGet row j) (by omega)
      simp only [Array.length_toList, size_zero_val] at *
      cost_simp
      split_ifs <;> omega

/-! ## A field inverse: Itoh–Tsujii, `10` squaring chains and `11` products -/

/-- `2^k`-th power by `k` squarings: `6 + 270·k` exactly (a square is a `GF(2^64)` product of
price `256`). -/
theorem powTwoPow_cost (hP : Includes P Auto.BF64.powTwoPow.c34.costDeps) :
    ∀ (k : ℕ) (a : BF64), k < 2 ^ 64 →
      machineCost P Auto.BF64.powTwoPow.c34.costIdx [encodeValue a, encodeValue k] =
      6 + 270 * k := by
  intro k
  induction k with
  | zero => intro a _; rw [Auto.BF64.powTwoPow.c34.costEq P hP]; cost_simp
  | succ k ih =>
    intro a hk
    rw [Auto.BF64.powTwoPow.c34.costEq P hP]
    cost_simp
    rw [ih (a * a) (by omega)]
    omega

/-- **A field inverse** (`BF64.invItohTsujii`): at most `19700`. -/
theorem invK_cost (hP : Includes P Auto.BF64.invItohTsujii.c33.costDeps) (a : BF64) :
    machineCost P Auto.BF64.invItohTsujii.c33.costIdx [encodeValue a] ≤ 19700 := by
  have h26 : Includes P Auto.BF64.powTwoPow.c34.costDeps := by includes
  rw [Auto.BF64.invItohTsujii.c33.costEq P hP]
  simp (disch := omega) only [powTwoPow_cost P h26]
  split_ifs <;> omega

/-! ## Subtracting a scaled, shifted row -/

/-- One coefficient of `a − c·X^d·b`: at most `300`. -/
theorem subCoeff_cost
    (hP : Includes P rowSubScaledShift.c28.lam0.lam0.costDeps)
    (a : PolynomialRow K) (c : K) (d : ℕ) (b : PolynomialRow K) (j j' : ℕ) (hd : d < 2 ^ 64)
    (hj' : j' < 2 ^ 64) :
      machineCost P rowSubScaledShift.c28.lam0.lam0.costIdx [encodeValue a, encodeValue c, encodeValue d, encodeValue b, encodeValue j, encodeValue j']
        ≤ 300 := by
  rw [rowSubScaledShift.c28.lam0.lam0.costEq P hP,
    rowGet_cost P (by includes), rowGet_cost P (by includes)]
  cost_simp
  split_ifs <;> omega

/-- `trimLen p n`: at most `22·n + 6`. -/
theorem trimLen_cost (hP : Includes P Auto.LeanVM.Cost.CompPolyLib.trimLen.c31.costDeps)
    (p : Array K) : ∀ n : ℕ, n < 2 ^ 64 →
      machineCost P Auto.LeanVM.Cost.CompPolyLib.trimLen.c31.costIdx [encodeValue p, encodeValue n] ≤
        22 * n + 6 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.LeanVM.Cost.CompPolyLib.trimLen.c31.costEq P hP]; cost_simp; omega
  | succ k ih =>
    intro hk
    rw [Auto.LeanVM.Cost.CompPolyLib.trimLen.c31.costEq P hP]
    have := ih (by omega)
    cost_simp
    split_ifs <;> omega

/-- `CPolynomial.ofArray`, trimming: at most `23·|coeffs| + 16`. -/
theorem ofArray_cost (hP : Includes P Auto.CompPoly.CPolynomial.ofArray.c30.costDeps)
    (coeffs : Array K) (hs : coeffs.size < 2 ^ 64) :
    machineCost P Auto.CompPoly.CPolynomial.ofArray.c30.costIdx [encodeValue coeffs] ≤
      23 * coeffs.size + 16 := by
  rw [Auto.CompPoly.CPolynomial.ofArray.c30.costEq P hP]
  have := trimLen_cost P (by includes) coeffs coeffs.size hs
  have : (coeffs.extract 0 (CompPolyLib.trimLen coeffs coeffs.size)).size ≤ coeffs.size := by
    simp
  cost_simp
  omega

/-- One entry of `a − c·X^d·b` (`subMulMonomial`, its `max(|aⱼ|, d + |bⱼ|)` coefficients and the
trim): at most `370·(D + d) + 200`. -/
theorem subMulMonomialEntry_cost
    (hP : Includes P rowSubScaledShift.c28.lam0.costDeps)
    {C D : ℕ} (a : PolynomialRow K) (ha : RowWithin C D a) (c : K) (d : ℕ) (hd : D + d < 2 ^ 62)
    (b : PolynomialRow K) (hb : RowWithin C D b) (j : ℕ) :
    machineCost P rowSubScaledShift.c28.lam0.costIdx [encodeValue a, encodeValue c, encodeValue d, encodeValue b, encodeValue j] ≤
      370 * (D + d) + 200 := by
  rw [rowSubScaledShift.c28.lam0.costEq P hP]
  have := rowGet_cost P (by includes) a j
  have := rowGet_cost P (by includes) b j
  have hsa := ha.size_rowGet j
  have hsb := hb.size_rowGet j
  have := listBeqK_cost P (by includes) (rowGet b j).val.toList
    (↑(0 : CPolynomial K) : Array K).toList
  have hm : max (rowGet a j).val.size (d + (rowGet b j).val.size) ≤ D + d := by omega
  have := rangeLoop_cost P (by includes) (max (rowGet a j).val.size (d + (rowGet b j).val.size))
    [] (by omega)
  have hf := fun j' ↦ RunsApp.of_spec (us := [encodeValue a, encodeValue c, encodeValue d, encodeValue b, encodeValue j]) (vs := [encodeValue j'])
    (rowSubScaledShift.c28.lam0.lam0.costSpec P (by includes)
      a c d b j j')
  have := listMap_le P Auto.List.map.c12.costIdx
    (.closure rowSubScaledShift.c28.lam0.lam0.costIdx
      [encodeValue a, encodeValue c, encodeValue d, encodeValue b, encodeValue j])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) 300
    (List.range (max (rowGet a j).val.size (d + (rowGet b j).val.size)))
    (fun j' hj' ↦ by
      rw [List.mem_range] at hj'
      rw [appCost_fn]
      exact subCoeff_cost P (by includes) a c d b j j' (by omega) (by omega))
  have := ofArray_cost P (by includes)
    ((List.range (max (rowGet a j).val.size (d + (rowGet b j).val.size))).map fun j' ↦
      (rowGet a j).coeff j' - if d ≤ j' then c * (rowGet b j).coeff (j' - d) else 0).toArray
    (by simp; omega)
  simp only [Array.length_toList, size_zero_val, List.length_range, List.length_map,
    List.size_toArray] at *
  cost_simp
  split_ifs <;> omega

/-- **`a − c·X^d·b`, row by row** (`rowSubScaledShift`): at most
`370·(D + d)·C + 230·C + 40`. -/
theorem rowSubScaledShift_cost
    (hP : Includes P rowSubScaledShift.c28.costDeps)
    {C D : ℕ} (hC : C < 2 ^ 62) (a : PolynomialRow K) (ha : RowWithin C D a) (c : K) (d : ℕ)
    (hd : D + d < 2 ^ 62) (b : PolynomialRow K) (hb : RowWithin C D b) :
    machineCost P rowSubScaledShift.c28.costIdx [encodeValue a, encodeValue c, encodeValue d, encodeValue b] ≤
      370 * ((D + d) * C) + 230 * C + 40 := by
  rw [rowSubScaledShift.c28.costEq P hP]
  have hm : max a.size b.size ≤ C := by have := ha.1; have := hb.1; omega
  have := rangeLoop_cost P (by includes) (max a.size b.size) [] (by omega)
  have hf := fun j ↦ RunsApp.of_spec (us := [encodeValue a, encodeValue c, encodeValue d, encodeValue b]) (vs := [encodeValue j])
    (rowSubScaledShift.c28.lam0.costSpec P (by includes) a c d b j)
  have hmap := listMap_le P Auto.List.map.c12.costIdx
    (.closure rowSubScaledShift.c28.lam0.costIdx [encodeValue a, encodeValue c, encodeValue d, encodeValue b])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) (370 * (D + d) + 200) (List.range
      (max a.size b.size))
    (fun j _ ↦ by
      rw [appCost_fn]
      exact subMulMonomialEntry_cost P (by includes) a ha c d hd b hb j)
  have := affine_mul_le' 370 200 11 (D + d) (max a.size b.size) C hm
  simp only [List.length_range, List.length_map] at *
  cost_simp
  split_ifs <;> omega

/-! ## The step -/

/-- **Cancelling a shifted leading term** (`cancelShiftedLeadingTermFast`): at most
`740·D·C + 790·C + 30·D + 21000` (two leading terms, an inverse, the row subtraction). -/
theorem cancelShiftedLeadingTerm_cost
    (hP : Includes P cancelShiftedLeadingTermFast.c25.costDeps)
    {C D S : ℕ} (hC : C < 2 ^ 62) (hDS : 2 * D + S < 2 ^ 62) (target reducer : PolynomialRow K)
    (ht : RowWithin C D target) (hr : RowWithin C D reducer) (shift : Array ℕ)
    (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P cancelShiftedLeadingTermFast.c25.costIdx [encodeValue target, encodeValue reducer, encodeValue shift] ≤
      740 * (D * C) + 790 * C + 30 * D + 21000 := by
  rw [cancelShiftedLeadingTermFast.c25.costEq P hP]
  have := rowShiftedLeadingTerm_cost P (by includes) hC (by omega) target ht shift hS
  have := rowShiftedLeadingTerm_cost P (by includes) hC (by omega) reducer hr shift hS
  generalize htt : rowShiftedLeadingTerm? target shift = o
  cases o with
  | none => dsimp only; omega
  | some t =>
    generalize hrt : rowShiftedLeadingTerm? reducer shift = o'
    cases o' with
    | none => dsimp only; omega
    | some r =>
      obtain ⟨htp, htd⟩ := rowShiftedLeadingTerm?_spec ht htt
      obtain ⟨hrp, hrd⟩ := rowShiftedLeadingTerm?_spec hr hrt
      have := ht.1
      have := hr.1
      have := invK_cost P (by includes) r.coeff
      have := rowSubScaledShift_cost P (by includes) hC target ht (t.coeff / r.coeff)
        (t.degree - r.degree) (by omega) reducer hr
      have : (D + (t.degree - r.degree)) * C ≤ 2 * (D * C) := by
        have := Nat.mul_le_mul_right C (show D + (t.degree - r.degree) ≤ 2 * D by omega)
        rwa [Nat.mul_assoc] at this
      dsimp only
      cost_simp
      split_ifs <;> omega

/-- **One Mulders–Storjohann step over `K`** (`muldersStorjohannStepFast M shift i j`, compiled
as `msStepK`): at most `|M| + 740·D·C + 970·C + 30·D + 21100`, for a matrix of rows of at most
`C` entries of at most `D` coefficients and shifts at most `S` (all word-sized). -/
theorem msStep_cost (hP : Includes P msStepK.costDeps) {C D S : ℕ} (hC : C < 2 ^ 62)
    (hDS : 2 * D + S < 2 ^ 62) (M : PolynomialMatrix K) (hM : ∀ row ∈ M, RowWithin C D row)
    (hMs : M.size < 2 ^ 64) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) (i j : ℕ) :
    machineCost P msStepK.costIdx [encodeValue M, encodeValue shift, encodeValue i, encodeValue j] ≤
      M.size + 740 * (D * C) + 970 * C + 30 * D + 21100 := by
  have hrow : ∀ k, RowWithin C D (M.getD k #[]) := by
    intro k
    rw [Array.getD_eq_getD_getElem?]
    cases hk : M[k]? with
    | none => exact RowWithin.empty C D
    | some row => exact hM row (Array.mem_of_getElem? hk)
  rw [msStepK.costEq P hP]
  have := rowShiftedDegree_cost P (by includes) hC (by omega) (M.getD i #[]) (hrow i) shift hS
  have := rowShiftedDegree_cost P (by includes) hC (by omega) (M.getD j #[]) (hrow j) shift hS
  have := cancelShiftedLeadingTerm_cost P (by includes) hC hDS (M.getD j #[]) (M.getD i #[])
    (hrow j) (hrow i) shift hS
  have := cancelShiftedLeadingTerm_cost P (by includes) hC hDS (M.getD i #[]) (M.getD j #[])
    (hrow i) (hrow j) shift hS
  generalize hi : rowShiftedDegree? (M.getD i #[]) shift = o
  cases o with
  | none => dsimp only; cost_simp; omega
  | some degI =>
    generalize hj : rowShiftedDegree? (M.getD j #[]) shift = o'
    cases o' with
    | none => dsimp only; cost_simp; omega
    | some degJ =>
      have := rowShiftedDegree?_le (hrow i) hS hi
      have := rowShiftedDegree?_le (hrow j) hS hj
      dsimp only
      cost_simp
      split_ifs <;> omega

end

end LeanVM.Cost.Bounds.Samples
