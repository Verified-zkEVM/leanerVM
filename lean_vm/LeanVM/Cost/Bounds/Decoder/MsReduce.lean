module

public import LeanVM.Cost.Bounds.Decoder.MsStep
public import LeanVM.Cost.Bounds.MuldersStorjohann
public import LeanVM.Cost.Bounds.Decoder.ShapeDefs

/-!
# Bound: Mulders–Storjohann's reduction, compiled

The price of the compiled reduction (`Cost/Extractor/MsReduce.lean`, `msReduceK`, CompPoly's
`muldersStorjohannReduceFast` over `K`) on a matrix of the loop's invariant (`MsInv r w D`:
`r` rows of width `w`, shifted degrees at most `D`), from the per-iteration price and the
number of iterations (`msLoop_cost_le`, `Bounds/MuldersStorjohann.lean`): `msReduceC_cost`, and on a
lane (`laneMsReduce_cost`; at `(28, 4)`, `laneMsReduce_cost_28_4`: `≈ 2^111.67` per lane, the
step's row subtraction over `w` entries of `D` coefficients dominating). One iteration:

* the rows' shifted leading positions (`rowLeadingPositionsC_cost`: `190·w·r + 118·r + 10`);
* the first pair of rows with the same position (`cachedLeadingConflictC_cost`, all pairs:
  `64·r² + 64·r + 19`);
* one step (`stepFastC_cost`, from its callees' bounds, `Bounds/Decoder/MsStep.lean`).
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly CompPoly.PolynomialMatrix LeanVM.Extraction

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.CompPoly.PolynomialMatrix

public section

/-! ## The invariant's rows -/

/-- Under the loop's invariant every row has width `w` and entries of at most `D + 1`
coefficients. -/
theorem rowWithin_of_msInv {r w D : ℕ} {M : PolynomialMatrix K} {shift : Array ℕ}
    (h : MsInv r w D M shift) (k : ℕ) : RowWithin w (D + 1) (M.getD k #[]) := by
  obtain ⟨hr, hw, hW, hD⟩ := h
  rw [Array.getD_eq_getD_getElem?]
  cases hk : M[k]? with
  | none => exact RowWithin.empty w (D + 1)
  | some row =>
    have hkM : k < M.size := by
      rcases Nat.lt_or_ge k M.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hk; cases hk
    have hrow : M.getD k #[] = row := by
      rw [Array.getD_eq_getD_getElem?, hk]; rfl
    change row.size ≤ w ∧ ∀ e ∈ row, e.val.size ≤ D + 1
    refine ⟨?_, ?_⟩
    · have := hW row (by simpa [MatrixRows] using Array.mem_of_getElem? hk)
      omega
    · intro e he
      obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem he
      have := entry_size_le' hD hkM j
      rw [hrow] at this
      have hg : rowGet row j = row[j] := by
        rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]; rfl
      rw [hg] at this
      exact this

theorem rowWithin_mem_of_msInv {r w D : ℕ} {M : PolynomialMatrix K} {shift : Array ℕ}
    (h : MsInv r w D M shift) : ∀ row ∈ M, RowWithin w (D + 1) row := by
  intro row hm
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hm
  have := rowWithin_of_msInv h k
  rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk] at this

variable (P : Program)

/-! ## The conflict search -/

/-- `List.range' start n`: at most `21·n + 6`. -/
theorem rangeC_cost (hP : Includes P Auto.List.range'.c10.costDeps) :
    ∀ (n start : ℕ), start + n < 2 ^ 63 →
      machineCost P Auto.List.range'.c10.costIdx [enc start, enc n, enc 1] ≤ 21 * n + 6 := by
  intro n
  induction n with
  | zero => intro start _; rw [Auto.List.range'.c10.costEq_zero P hP]
  | succ n ih =>
    intro start h
    rw [Auto.List.range'.c10.costEq_succ P hP]
    have := ih (start + 1) (by omega)
    cost_simp
    omega

/-- The positions are word-sized. -/
@[expose] def WordPositions (positions : Array (Option ℕ)) : Prop :=
  ∀ i v, positions.getD i none = some v → v < 2 ^ 64

/-- One comparison of two rows' positions: at most `25`. -/
theorem conflictStepC_cost (hP : Includes P cachedLeadingConflictInRowStep?.c9.costDeps)
    (positions : Array (Option ℕ)) (hp : WordPositions positions) (i : ℕ)
    (found : Option (ℕ × ℕ)) (j : ℕ) :
    machineCost P cachedLeadingConflictInRowStep?.c9.costIdx
      [enc positions, enc i, enc found, enc j] ≤ 25 := by
  cases found with
  | some v => rw [cachedLeadingConflictInRowStep?.c9.costEq_some P hP]; omega
  | none =>
    rw [cachedLeadingConflictInRowStep?.c9.costEq_none P hP]
    generalize hi : positions.getD i none = oi
    generalize hj : positions.getD j none = oj
    cases oi with
    | none => dsimp only; omega
    | some a =>
      cases oj with
      | none => dsimp only; omega
      | some b =>
        have := hp i a hi
        have := hp j b hj
        dsimp only
        cost_simp
        split_ifs <;> omega

/-- The comparisons of row `i` with the later rows: at most `60·r + 30`. -/
theorem conflictRowC_cost (hP : Includes P cachedLeadingConflictInRow?.c7.costDeps)
    (positions : Array (Option ℕ)) (hp : WordPositions positions) (hr : positions.size < 2 ^ 62)
    (i : ℕ) (hi : i < positions.size) (found : Option (ℕ × ℕ)) :
    machineCost P cachedLeadingConflictInRow?.c7.costIdx [enc positions, enc i, enc found] ≤
      60 * positions.size + 30 := by
  rw [cachedLeadingConflictInRow?.c7.costEq P hP]
  have := rangeC_cost P (by includes) (positions.size - (i + 1)) (i + 1) (by omega)
  have hf := listFoldl_le P (by includes) _
    (.fn cachedLeadingConflictInRow?.c7.lam0.costIdx [enc positions, enc i])
    (fun found j ↦ RunsApp.of_spec (us := [enc positions, enc i]) (vs := [enc found, enc j])
      (cachedLeadingConflictInRow?.c7.lam0.costSpec P (by includes) positions i found j))
    30 (fun _ ↦ True) (List.range' (i + 1) (positions.size - (i + 1))) found trivial
    (fun acc _ j _ ↦ ⟨trivial, by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        cachedLeadingConflictInRow?.c7.lam0.costEq P (by includes)]
      have := conflictStepC_cost P (by includes) positions hp i acc j
      omega⟩)
  simp only [List.length_range'] at hf
  cost_simp
  have : (30 + 9) * (positions.size - (i + 1)) ≤ 39 * positions.size := by
    have := Nat.sub_le positions.size (i + 1)
    omega
  omega

/-- **The first conflict** (`cachedLeadingConflict?`, every pair of rows): at most
`64·r² + 64·r + 19` (`r·r` an atom for `omega`). -/
theorem cachedLeadingConflictC_cost (hP : Includes P cachedLeadingConflict?.c5.costDeps)
    (positions : Array (Option ℕ)) (hp : WordPositions positions)
    (hr : positions.size < 2 ^ 62) :
    machineCost P cachedLeadingConflict?.c5.costIdx [enc positions] ≤
      64 * (positions.size * positions.size) + 64 * positions.size + 19 := by
  rw [cachedLeadingConflict?.c5.costEq P hP]
  have := rangeC_cost P (by includes) positions.size 0 (by omega)
  have hf := listFoldl_le P (by includes) _
    (.fn cachedLeadingConflict?.c5.lam0.costIdx [enc positions])
    (fun found i ↦ RunsApp.of_spec (us := [enc positions]) (vs := [enc found, enc i])
      (cachedLeadingConflict?.c5.lam0.costSpec P (by includes) positions found i))
    (60 * positions.size + 34) (fun _ ↦ True) (List.range' 0 positions.size) none trivial
    (fun acc _ i hi ↦ ⟨trivial, by
      rw [List.mem_range'] at hi
      rw [appCost_fn, List.cons_append, List.nil_append,
        cachedLeadingConflict?.c5.lam0.costEq P (by includes)]
      have := conflictRowC_cost P (by includes) positions hp hr i (by omega) acc
      omega⟩)
  simp only [List.length_range'] at hf
  have := affine_mul_le' 60 34 9 positions.size positions.size positions.size le_rfl
  omega

/-! ## One iteration -/

/-- **One step** (`muldersStorjohannStepFast.c24`): at most
`|M| + 740·D·C + 970·C + 30·D + 21100`. -/
theorem stepFastC_cost (hP : Includes P muldersStorjohannStepFast.c24.costDeps) {C D S : ℕ}
    (hC : C < 2 ^ 62) (hDS : 2 * D + S < 2 ^ 62) (M : PolynomialMatrix K)
    (hM : ∀ row ∈ M, RowWithin C D row) (hMs : M.size < 2 ^ 64) (shift : Array ℕ)
    (hS : ∀ j, shift.getD j 0 ≤ S) (i j : ℕ) :
    machineCost P muldersStorjohannStepFast.c24.costIdx [enc M, enc shift, enc i, enc j] ≤
      M.size + 740 * (D * C) + 970 * C + 30 * D + 21100 := by
  have hrow : ∀ k, RowWithin C D (M.getD k #[]) := by
    intro k
    rw [Array.getD_eq_getD_getElem?]
    cases hk : M[k]? with
    | none => exact RowWithin.empty C D
    | some row => exact hM row (Array.mem_of_getElem? hk)
  rw [muldersStorjohannStepFast.c24.costEq P hP]
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

/-- **The rows' shifted leading positions** (`rowLeadingPositions`): at most
`190·C·r + 118·r + 10` for `r` rows of the bounds. -/
theorem rowLeadingPositionsC_cost (hP : Includes P rowLeadingPositions.c11.costDeps) {C D S : ℕ}
    (hC : C < 2 ^ 62) (hDS : D + S < 2 ^ 62) (M : PolynomialMatrix K)
    (hM : ∀ row ∈ M, RowWithin C D row) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P rowLeadingPositions.c11.costIdx [enc M, enc shift] ≤
      190 * (C * M.size) + 118 * M.size + 10 := by
  rw [rowLeadingPositions.c11.costEq P hP]
  have hf := fun row ↦ RunsApp.of_spec (us := [enc shift]) (vs := [enc row])
    (rowLeadingPositions.c11.lam0.costSpec P (by includes) shift row)
  have hmap := listMap_le P Auto.List.map.c12.costIdx
    (.fn rowLeadingPositions.c11.lam0.costIdx [enc shift])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) (190 * C + 103) M.toList
    (fun row hrow ↦ by
      rw [appCost_fn, List.singleton_append, rowLeadingPositions.c11.lam0.costEq P (by includes)]
      have := rowShiftedLeadingPosition_cost P (by includes) hC hDS row
        (hM row (by simpa using hrow)) shift hS
      omega)
  have := affine_mul_le' 190 103 11 C M.size M.size le_rfl
  simp only [Array.length_toList, List.length_map] at hmap ⊢
  omega

/-- The rows' leading positions are word-sized (each is in its row). -/
theorem wordPositions_rowLeadingPositions {C D : ℕ} (hC : C < 2 ^ 62) (M : PolynomialMatrix K)
    (hM : ∀ row ∈ M, RowWithin C D row) (shift : Array ℕ) :
    WordPositions (rowLeadingPositions M shift) := by
  intro i v hv
  rw [rowLeadingPositions, Array.getD_eq_getD_getElem?, Array.getElem?_map] at hv
  cases hk : M[i]? with
  | none => simp [hk] at hv
  | some row =>
    simp only [hk, Option.map_some, Option.getD_some] at hv
    have := rowShiftedLeadingPosition?_lt hv
    have := (hM row (Array.mem_of_getElem? hk)).1
    omega

/-! ## The loop -/

/-- **The loop** (`muldersStorjohannReduceWithFuelFast`): at most
`(r·(D + 1)·(w + 1) + 1)·msIterBound r w D`, whatever the fuel (below `2^64`). -/
theorem msLoopC_cost (hP : Includes P muldersStorjohannReduceWithFuelFast.c4.costDeps)
    {r w D S : ℕ} (hr : r < 2 ^ 62) (hw : w < 2 ^ 62) (hDS : 2 * (D + 1) + S < 2 ^ 62)
    (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    ∀ (fuel : ℕ) (M : PolynomialMatrix K), fuel < 2 ^ 64 → MsInv r w D M shift →
      machineCost P muldersStorjohannReduceWithFuelFast.c4.costIdx [enc fuel, enc M, enc shift] ≤
        (r * ((D + 1) * (w + 1)) + 1) * msIterBound r w D := by
  intro fuel M hf hM
  have key := msLoop_cost_le (F := K) (r := r) (w := w) (D := D) (shift := shift)
    (c := msIterBound r w D)
    (fun fuel M ↦ if fuel < 2 ^ 64 then
      machineCost P muldersStorjohannReduceWithFuelFast.c4.costIdx [enc fuel, enc M, enc shift]
      else 0)
    (fun M _ ↦ by
      simp only [show (0 : ℕ) < 2 ^ 64 by norm_num, ↓reduceIte]
      rw [muldersStorjohannReduceWithFuelFast.c4.costEq_zero P hP]
      unfold msIterBound
      omega)
    (fun fuel M hM ↦ by
      by_cases h : fuel + 1 < 2 ^ 64
      · simp only [h, ↓reduceIte, show fuel < 2 ^ 64 by omega]
        rw [muldersStorjohannReduceWithFuelFast.c4.costEq_succ P hP]
        have hrows := rowWithin_mem_of_msInv hM
        have hMr : M.size = r := hM.1
        have h1 := rowLeadingPositionsC_cost P (by includes) hw (by omega) M hrows shift
          (S := S) (fun j ↦ hS j)
        rw [hMr] at h1
        have hpos := wordPositions_rowLeadingPositions hw M hrows shift
        have hps : (rowLeadingPositions M shift).size = r := by simp [rowLeadingPositions, hMr]
        have h2 := cachedLeadingConflictC_cost P (by includes) _ hpos (by omega)
        rw [hps] at h2
        cost_simp
        unfold msIterBound
        cases hc : cachedLeadingConflict? (rowLeadingPositions M shift) with
        | none => dsimp only; omega
        | some ij =>
          obtain ⟨i, j⟩ := ij
          have h3 := stepFastC_cost P (by includes) hw (by omega) M hrows (by omega) shift hS i j
          rw [hMr] at h3
          dsimp only
          omega
      · simp only [h, ↓reduceIte]
        omega)
    fuel hM
  simpa only [hf, ↓reduceIte] using key

/-! ## The fuel and the reduction -/

/-- The matrix's shifted degree is at most `D + 1 + S` (the rows' are). -/
theorem matrixShiftedDegree?_le {r w D S : ℕ} {M : PolynomialMatrix K} {shift : Array ℕ}
    (hM : MsInv r w D M shift) (hS : ∀ j, shift.getD j 0 ≤ S) :
    ∀ (l : List ℕ) (acc : Option ℕ), (∀ v, acc = some v → v ≤ D + 1 + S) →
      ∀ v, l.foldl (fun acc i ↦ match rowShiftedDegree? (M.getD i #[]) shift with
        | none => acc
        | some d => maxOption acc d) acc = some v → v ≤ D + 1 + S := by
  intro l
  induction l with
  | nil => intro acc hacc v hv; exact hacc v hv
  | cons i l ih =>
    intro acc hacc
    apply ih
    intro v hv
    dsimp only at hv
    generalize he : rowShiftedDegree? (M.getD i #[]) shift = o at hv
    cases o with
    | none => exact hacc v hv
    | some d =>
      have hd := rowShiftedDegree?_le (rowWithin_of_msInv hM i) hS he
      cases acc with
      | none => simp only [maxOption, Option.some.injEq] at hv; omega
      | some m =>
        have := hacc m rfl
        simp only [maxOption, Option.some.injEq] at hv
        omega

theorem matrixShiftedDegree_getD_le {r w D S : ℕ} {M : PolynomialMatrix K} {shift : Array ℕ}
    (hM : MsInv r w D M shift) (hS : ∀ j, shift.getD j 0 ≤ S) :
    (matrixShiftedDegree? M shift).getD 0 ≤ D + 1 + S := by
  cases h : matrixShiftedDegree? M shift with
  | none => simp
  | some d => exact matrixShiftedDegree?_le hM hS _ none (by simp) d h

/-- **The matrix's shifted degree** (`matrixShiftedDegree?`): at most `90·w·r + 77·r + 20`. -/
theorem matrixShiftedDegreeC_cost (hP : Includes P matrixShiftedDegree?.c36.costDeps)
    {r w D S : ℕ} (hr : r < 2 ^ 62) (hw : w < 2 ^ 62) (hDS : 2 * (D + 1) + S < 2 ^ 62)
    (M : PolynomialMatrix K) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S)
    (hM : MsInv r w D M shift) :
    machineCost P matrixShiftedDegree?.c36.costIdx [enc M, enc shift] ≤
      90 * (w * r) + 77 * r + 20 := by
  have hMr : M.size = r := hM.1
  rw [matrixShiftedDegree?.c36.costEq P hP]
  have hl := rangeLoop_cost P (by includes) M.size [] (by omega)
  have hfold := listFoldl_le P (by includes) _
    (.fn matrixShiftedDegree?.c36.lam0.costIdx [enc M, enc shift])
    (fun acc i ↦ RunsApp.of_spec (us := [enc M, enc shift]) (vs := [enc acc, enc i])
      (matrixShiftedDegree?.c36.lam0.costSpec P (by includes) M shift acc i))
    (90 * w + 51) (fun acc ↦ ∀ v, acc = some v → v ≤ D + 1 + S) (List.range M.size) none
    (by simp)
    (fun acc hacc i _ ↦ by
      refine ⟨?_, ?_⟩
      · intro v hv
        generalize he : rowShiftedDegree? (M.getD i #[]) shift = o at hv
        cases o with
        | none => exact hacc v hv
        | some d =>
          have hd := rowShiftedDegree?_le (rowWithin_of_msInv hM i) hS he
          cases acc with
          | none => simp only [maxOption, Option.some.injEq] at hv; omega
          | some m =>
            have := hacc m rfl
            simp only [maxOption, Option.some.injEq] at hv
            omega
      · rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
          matrixShiftedDegree?.c36.lam0.costEq P (by includes)]
        have := rowShiftedDegree_cost P (by includes) hw (by omega) (M.getD i #[])
          (rowWithin_of_msInv hM i) shift hS
        generalize he : rowShiftedDegree? (M.getD i #[]) shift = o
        cases o with
        | none => dsimp only; omega
        | some d =>
          have := rowShiftedDegree?_le (rowWithin_of_msInv hM i) hS he
          have := maxOption_cost P (by includes) acc d (fun v hv ↦ by have := hacc v hv; omega)
            (by omega)
          dsimp only
          omega)
  simp only [List.length_range] at hfold
  have ha := affine_mul_le' 90 51 9 w M.size r (by omega)
  rw [hMr] at hfold ha hl ⊢
  omega

/-- The matrix's width: at most `15`. -/
theorem matrixWidthC_cost (hP : Includes P MatrixWidth.c38.costDeps) (M : PolynomialMatrix K)
    (hMs : M.size < 2 ^ 64) : machineCost P MatrixWidth.c38.costIdx [enc M] ≤ 15 := by
  rw [MatrixWidth.c38.costEq P hP]
  cost_simp
  cases M[0]? <;> dsimp only <;> split_ifs <;> omega

/-- **The fuel** (`muldersStorjohannFuel`): at most `90·w·r + 77·r + 60`. -/
theorem msFuelC_cost (hP : Includes P muldersStorjohannFuel.c35.costDeps)
    {r w D S : ℕ} (hr : r < 2 ^ 62) (hw : w < 2 ^ 62) (hDS : 2 * (D + 1) + S < 2 ^ 62)
    (hrw : (r + 1) * (w + 1) < 2 ^ 64) (M : PolynomialMatrix K) (shift : Array ℕ)
    (hS : ∀ j, shift.getD j 0 ≤ S) (hM : MsInv r w D M shift) :
    machineCost P muldersStorjohannFuel.c35.costIdx [enc M, enc shift] ≤
      90 * (w * r) + 77 * r + 60 := by
  have hMr : M.size = r := hM.1
  have hMw : MatrixWidth M = w := hM.2.1
  rw [muldersStorjohannFuel.c35.costEq P hP]
  have := matrixShiftedDegreeC_cost P (by includes) hr hw hDS M shift hS hM
  have := matrixWidthC_cost P (by includes) M (by omega)
  have := matrixShiftedDegree_getD_le hM hS
  rw [hMr, hMw]
  cost_simp
  cases matrixShiftedDegree? M shift <;> dsimp only <;> omega

/-- **Mulders–Storjohann's reduction, compiled** (`msReduceK`, `muldersStorjohannReduceFast`):
on `r` rows of width `w` with shifted degrees at most `D` and shifts at most `S`, at most
`(r·(D + 1)·(w + 1) + 1)·msIterBound r w D + 90·w·r + 77·r + 66`. -/
theorem msReduceC_cost (hP : Includes P msReduceK.costDeps) {r w D S : ℕ} (hr : r < 2 ^ 62)
    (hw : w < 2 ^ 62) (hDS : 2 * (D + 1) + S < 2 ^ 62)
    (hfuel : (r + 1) * (w + 1) * (D + S + 2) < 2 ^ 64) (M : PolynomialMatrix K)
    (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) (hM : MsInv r w D M shift) :
    machineCost P msReduceK.costIdx [enc M, enc shift] ≤
      (r * ((D + 1) * (w + 1)) + 1) * msIterBound r w D + 90 * (w * r) + 77 * r + 66 := by
  have hrw : (r + 1) * (w + 1) < 2 ^ 64 := by
    have : (r + 1) * (w + 1) * 1 ≤ (r + 1) * (w + 1) * (D + S + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  rw [msReduceK.costEq P hP]
  have := msFuelC_cost P (by includes) hr hw hDS hrw M shift hS hM
  have hf : muldersStorjohannFuel M shift < 2 ^ 64 := by
    have hd := matrixShiftedDegree_getD_le hM hS
    simp only [muldersStorjohannFuel, hM.1, hM.2.1]
    have : (r + 1) * (w + 1) * ((matrixShiftedDegree? M shift).getD 0 + 1) ≤
        (r + 1) * (w + 1) * (D + S + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have := msLoopC_cost P (by includes) hr hw hDS shift hS _ M hf hM
  omega

/-! ## On a lane -/

/-- The lane's shifts: `shift[j] = j·(k − 1)` for the `ℓ + 1` columns, at most `ℓ·(k − 1)`. -/
theorem laneShifts_le (κ R A j : ℕ) :
    (GuruswamiSudan.leeOSullivanShifts (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp).getD j 0 ≤
      laneYCap κ R A * (2 ^ κ - 1) := by
  unfold GuruswamiSudan.leeOSullivanShifts GuruswamiSudan.leeOSullivanWidth
  by_cases hj :
    j < GuruswamiSudan.interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp + 1
  · rw [weightedDegreeShift_getD _ _ _ hj]
    simp only [laneYCap, GuruswamiSudan.yWeight, gsParamsFor, gsParamsAt] at hj ⊢
    exact Nat.mul_le_mul_right _ (by omega)
  · simp [CBivariate.weightedDegreeShift, Array.getD_eq_getD_getElem?, Nat.not_lt.1 hj]

/-- The bound of a lane's reduction: `r = ℓ + 1` rows and columns, degrees `D = m·n + ℓ·(k − 1)`. -/
@[expose] def laneMsBound (κ R A : ℕ) : ℕ :=
  (laneYCap κ R A + 1) * ((laneDegBound κ R A + 1) * (laneYCap κ R A + 2)) *
      msIterBound (laneYCap κ R A + 1) (laneYCap κ R A + 1) (laneDegBound κ R A) +
    msIterBound (laneYCap κ R A + 1) (laneYCap κ R A + 1) (laneDegBound κ R A) +
    90 * ((laneYCap κ R A + 1) * (laneYCap κ R A + 1)) + 77 * (laneYCap κ R A + 1) + 66

/-- **A lane's Mulders–Storjohann reduction** (Lee–O'Sullivan's basis of the lane, its shifts):
at most `laneMsBound κ R A`, when the sizes are word-sized. -/
theorem laneMsReduce_cost (hP : Includes P msReduceK.costDeps) (κ R A : ℕ) (W : ℕ → List K)
    (u : ℕ) (hr : laneYCap κ R A + 1 < 2 ^ 62)
    (hDS : 2 * (laneDegBound κ R A + 1) + laneYCap κ R A * (2 ^ κ - 1) < 2 ^ 62)
    (hfuel : (laneYCap κ R A + 2) * (laneYCap κ R A + 2) *
      (laneDegBound κ R A + laneYCap κ R A * (2 ^ κ - 1) + 2) < 2 ^ 64) :
    machineCost P msReduceK.costIdx [enc (laneBasis κ R A W u),
        enc (GuruswamiSudan.leeOSullivanShifts (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp)] ≤
      laneMsBound κ R A := by
  have := msReduceC_cost P hP hr hr hDS hfuel (laneBasis κ R A W u) _ (laneShifts_le κ R A)
    (laneBasis_msInv κ R A W u)
  unfold laneMsBound
  rw [Nat.add_mul, Nat.one_mul] at this
  exact this

/-- **At the worst shape `(28, 4)`** (`k = 2^22`, `n = 2^26`, `A = 16792398`: `ℓ = 1661`,
`m = 415`, `D = 34816915843`): a lane's reduction costs at most
`4120758887382473769018615478698110 ≈ 2^111.67` (`≈ 2^117.67` over the 64 lanes). -/
theorem laneMsReduce_cost_28_4 (hP : Includes P msReduceK.costDeps) (W : ℕ → List K) (u : ℕ) :
    machineCost P msReduceK.costIdx [enc (laneBasis 22 4 16792398 W u),
        enc (GuruswamiSudan.leeOSullivanShifts
          (gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp)] ≤
      4120758887382473769018615478698110 := by
  have := laneMsReduce_cost P hP 22 4 16792398 W u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have h : laneMsBound 22 4 16792398 = 4120758887382473769018615478698110 := by decide +kernel
  omega

end

end LeanVM.Cost.Bounds.Decoder
