module

public import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness
public import CompPoly.Bivariate.ToPoly
public import Statement.Extractor
import all CompPoly.Univariate.Basic

/-!
# Mulders–Storjohann: the number of steps and the degrees

CompPoly's Mulders–Storjohann reduction (`muldersStorjohannReduceFast`, the reducer of the
extractor's Lee–O'Sullivan interpolation) repeats, while two nonzero rows have the same shifted
leading position, a simple transformation: the row of larger shifted degree loses its leading
term against the other. Its time is bounded through two facts about this loop:

* **the degrees never grow** (`ShiftedDegreeLe`, `muldersStorjohannStepFast_shiftedDegreeLe`):
  if every nonzero entry `M[i][j]` has `deg M[i][j] + shift[j] ≤ D`, the step keeps it so, and
  every entry is an array of at most `D + 1` coefficients (`entry_size_le`); the shift `c·X^d`
  of a step has `d + |b_j| ≤ D + 1` for every reducer entry `b_j` (`cancel_shift_add_size_le`),
  so the fused update `a - c·X^d·b` builds arrays of at most `D + 1` coefficients;
* **a step decreases CompPoly's termination measure** (`shiftedMatrixMeasure`, the sum over rows
  of `deg·(w + 1) + pos + 1`; CompPoly's `muldersStorjohannStep_shiftedMatrixMeasure_lt`), which
  is at most `r·(D + 1)·(w + 1)` for `r` rows of width `w`
  (`shiftedMatrixMeasure_le_of_shiftedDegreeLe`).

Hence **`msStepCount_le`**: the loop makes at most `r·(D + 1)·(w + 1)` steps, and
**`msLoop_cost_le`**: any cost function of the loop that pays at most `c` per iteration on
matrices of `r` rows, width `w` and degrees `≤ D` is at most `(r·(D + 1)·(w + 1) + 1)·c`.

**Lee–O'Sullivan's initial basis** (`leeOSullivanBasisRows_msInv`): `ℓ + 1` rows of width
`ℓ + 1`, `ℓ = ⌊W/(k − 1)⌋`, every shifted degree at most `D = m·n + ℓ·(k − 1)` (row `i` is
`Y^(i−t)·(Y − R)^t·G^(m−t)` with `deg G ≤ n` the vanishing polynomial, `deg R ≤ deg G`). At the
decoder's parameters (`laneBasis_msInv`, `laneStepCount_le`, `laneDegBound_le`): at most
`(ℓ + 1)·(D + 1)·(ℓ + 2)` steps, `D ≤ m·n + W`; at the worst shape `(28, 4)` (`k = 2^22`,
`n = 2^26`, `A = 16792398`, `m = 415`, `ℓ = 1661`): `D = 34816915843 ≈ 2^35.02` and at most
`≈ 2^56.42` steps.

Credits: the loop, its termination measure and the leading-term lemmas used here are CompPoly's
(github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly Contributors";
`LinearAlgebra/PolynomialMatrix/MuldersStorjohann.lean` and `MuldersStorjohannCorrectness/`,
Valerii Huhnin), used, not copied. Reference: T. Mulders and A. Storjohann, *On lattice reduction
for polynomial matrices*, J. Symbolic Comput. 35 (2003), §2–3 (the simple transformations; the
count of steps by a degree potential).
-/

namespace LeanVM.Cost.Bounds

open CompPoly CompPoly.PolynomialMatrix

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-! ## The degree invariant -/

/-- **Every nonzero entry has shifted degree at most `D`**: `deg M[i][j] + shift[j] ≤ D`. -/
@[expose] def ShiftedDegreeLe (M : PolynomialMatrix F) (shift : Array Nat) (D : ℕ) : Prop :=
  ∀ i, i < M.size → ∀ j, rowGet (M.getD i #[]) j ≠ 0 →
    (rowGet (M.getD i #[]) j).natDegree + shift.getD j 0 ≤ D

/-- The invariant of the loop: `r` rows of width `w`, rectangular, degrees at most `D`. -/
@[expose] def MsInv (r w D : ℕ) (M : PolynomialMatrix F) (shift : Array Nat) : Prop :=
  M.size = r ∧ MatrixWidth M = w ∧ WellFormed M ∧ ShiftedDegreeLe M shift D

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- A canonical polynomial of degree `d` is an array of at most `d + 1` coefficients. -/
theorem val_size_le_natDegree_add_one (p : CPolynomial F) : p.val.size ≤ p.natDegree + 1 := by
  unfold CPolynomial.natDegree
  split <;> omega

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- **Entry sizes**: under the invariant, every entry `M[i][j]` is an array of at most
`D + 1 - shift[j]` coefficients. -/
theorem entry_size_le {M : PolynomialMatrix F} {shift : Array Nat} {D : ℕ}
    (h : ShiftedDegreeLe M shift D) {i : ℕ} (hi : i < M.size) (j : ℕ) :
    (rowGet (M.getD i #[]) j).val.size + shift.getD j 0 ≤ D + 1 ∨
      (rowGet (M.getD i #[]) j).val.size = 0 := by
  by_cases h0 : rowGet (M.getD i #[]) j = 0
  · right; rw [h0]; rfl
  · left
    have := h i hi j h0
    have := val_size_le_natDegree_add_one (rowGet (M.getD i #[]) j)
    omega

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- Entry sizes, plainly: at most `D + 1` coefficients. -/
theorem entry_size_le' {M : PolynomialMatrix F} {shift : Array Nat} {D : ℕ}
    (h : ShiftedDegreeLe M shift D) {i : ℕ} (hi : i < M.size) (j : ℕ) :
    (rowGet (M.getD i #[]) j).val.size ≤ D + 1 := by
  rcases entry_size_le h hi j with h | h <;> omega

omit [DecidableEq F] in
theorem rowShiftedDegree_le_of_entries {row : PolynomialRow F} {shift : Array Nat} {D d : ℕ}
    (hb : ∀ j, rowGet row j ≠ 0 → (rowGet row j).natDegree + shift.getD j 0 ≤ D)
    (h : rowShiftedDegree? row shift = some d) : d ≤ D :=
  rowShiftedDegree?_le_of_entry_bound (fun k _ hk ↦ hb k hk) h

omit [DecidableEq F] in
theorem rowShiftedDegree_le {M : PolynomialMatrix F} {shift : Array Nat} {D : ℕ}
    (h : ShiftedDegreeLe M shift D) {i d : ℕ} (hi : i < M.size)
    (hd : rowShiftedDegree? (M.getD i #[]) shift = some d) : d ≤ D :=
  rowShiftedDegree_le_of_entries (h i hi) hd

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem rowGet_eq_zero_of_size_le {row : PolynomialRow F} {j : ℕ} (hj : row.size ≤ j) :
    rowGet row j = 0 := by
  rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hj, Option.getD_none]

/-- **A cancellation keeps the degrees**: when the target's shifted degree is at least the
reducer's, every entry of the new target row is within the bound of the old one. -/
theorem cancel_entry_le {target reducer : PolynomialRow F} {shift : Array Nat} {D : ℕ}
    (hsize : reducer.size = target.size)
    (hb : ∀ j, rowGet target j ≠ 0 → (rowGet target j).natDegree + shift.getD j 0 ≤ D)
    (hle : ∀ dt dr, rowShiftedDegree? target shift = some dt →
      rowShiftedDegree? reducer shift = some dr → dr ≤ dt) :
    ∀ j, rowGet (cancelShiftedLeadingTerm target reducer shift) j ≠ 0 →
      (rowGet (cancelShiftedLeadingTerm target reducer shift) j).natDegree +
        shift.getD j 0 ≤ D := by
  intro j hj
  cases ht : rowShiftedLeadingTerm? target shift with
  | none =>
    have hc : cancelShiftedLeadingTerm target reducer shift = target := by
      simp [cancelShiftedLeadingTerm, ht]
    rw [hc] at hj ⊢
    exact hb j hj
  | some t =>
    cases hr : rowShiftedLeadingTerm? reducer shift with
    | none =>
      have hc : cancelShiftedLeadingTerm target reducer shift = target := by
        simp [cancelShiftedLeadingTerm, ht, hr]
      rw [hc] at hj ⊢
      exact hb j hj
    | some r =>
      by_cases hpos : t.position = r.position
      · obtain ⟨htd, -⟩ := rowShiftedLeadingTerm?_some_data ht
        obtain ⟨hrd, -⟩ := rowShiftedLeadingTerm?_some_data hr
        have hjlt : j < target.size := by
          by_contra hge
          apply hj
          apply rowGet_eq_zero_of_size_le
          rw [cancelShiftedLeadingTerm_size hsize]
          omega
        exact (cancelShiftedLeadingTerm_entry_bound ht hr hpos (hle _ _ htd hrd) hsize hjlt hj).trans
          (rowShiftedDegree_le_of_entries hb htd)
      · have hc : cancelShiftedLeadingTerm target reducer shift = target := by
          simp [cancelShiftedLeadingTerm, ht, hr, hpos]
        rw [hc] at hj ⊢
        exact hb j hj

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem rowGet_replaceRow_self (M : PolynomialMatrix F) (idx : ℕ) (row : PolynomialRow F)
    (hidx : idx < M.size) (j : ℕ) :
    rowGet ((replaceRow M idx row).getD idx #[]) j = rowGet row j := by
  simp [replaceRow, Array.getD_eq_getD_getElem?, hidx]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem rowGet_replaceRow_ne (M : PolynomialMatrix F) (idx k : ℕ) (row : PolynomialRow F)
    (hk : k ≠ idx) (j : ℕ) :
    rowGet ((replaceRow M idx row).getD k #[]) j = rowGet (M.getD k #[]) j := by
  have hne : idx ≠ k := fun h ↦ hk h.symm
  simp [replaceRow, Array.getD_eq_getD_getElem?, hne]

/-- **A step keeps the degrees** (any pair of rows). -/
theorem muldersStorjohannStep_shiftedDegreeLe {M : PolynomialMatrix F} {shift : Array Nat}
    {D : ℕ} (hM : WellFormed M) (h : ShiftedDegreeLe M shift D) (i j : ℕ) :
    ShiftedDegreeLe (muldersStorjohannStep M shift i j) shift D := by
  cases hI : rowShiftedDegree? (M.getD i #[]) shift with
  | none =>
    have e : muldersStorjohannStep M shift i j = M := by rw [muldersStorjohannStep]; simp only [hI]
    rwa [e]
  | some degI =>
    cases hJ : rowShiftedDegree? (M.getD j #[]) shift with
    | none =>
      have e : muldersStorjohannStep M shift i j = M := by
        rw [muldersStorjohannStep]; simp only [hI, hJ]
      rwa [e]
    | some degJ =>
      have hi : i < M.size := by
        by_contra hge
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at hI
        simp [rowShiftedDegree?] at hI
      have hj : j < M.size := by
        by_contra hge
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at hJ
        simp [rowShiftedDegree?] at hJ
      have hsz : (M.getD i #[]).size = (M.getD j #[]).size := by
        rw [matrix_getD_size_of_wellFormed hM hi, matrix_getD_size_of_wellFormed hM hj]
      have e : muldersStorjohannStep M shift i j =
          if degI ≤ degJ then
            replaceRow M j (cancelShiftedLeadingTerm (M.getD j #[]) (M.getD i #[]) shift)
          else replaceRow M i (cancelShiftedLeadingTerm (M.getD i #[]) (M.getD j #[]) shift) := by
        rw [muldersStorjohannStep]; simp only [hI, hJ]
      rw [e]
      by_cases hle : degI ≤ degJ
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hle)]
        intro k hk l hl
        rw [replaceRow_size] at hk
        by_cases hkj : k = j
        · rw [hkj] at hl ⊢
          rw [rowGet_replaceRow_self M j _ hj] at hl ⊢
          refine cancel_entry_le hsz (h j hj) ?_ l hl
          intro dt dr hdt hdr
          rw [hJ] at hdt
          rw [hI] at hdr
          cases hdt; cases hdr; exact hle
        · rw [rowGet_replaceRow_ne M j k _ hkj] at hl ⊢
          exact h k hk l hl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hle)]
        intro k hk l hl
        rw [replaceRow_size] at hk
        by_cases hki : k = i
        · rw [hki] at hl ⊢
          rw [rowGet_replaceRow_self M i _ hi] at hl ⊢
          refine cancel_entry_le hsz.symm (h i hi) ?_ l hl
          intro dt dr hdt hdr
          rw [hI] at hdt
          rw [hJ] at hdr
          cases hdt; cases hdr; omega
        · rw [rowGet_replaceRow_ne M i k _ hki] at hl ⊢
          exact h k hk l hl

/-- **The fast step keeps the invariant.** -/
theorem muldersStorjohannStepFast_msInv {r w D : ℕ} {M : PolynomialMatrix F}
    {shift : Array Nat} (h : MsInv r w D M shift) (i j : ℕ) :
    MsInv r w D (muldersStorjohannStepFast M shift i j) shift := by
  obtain ⟨hr, hw, hM, hD⟩ := h
  rw [muldersStorjohannStepFast_eq]
  have hshape := muldersStorjohannStep_shape_preserved shift (i := i) (j := j) hM
  simp only [MatrixShape, PolynomialMatrixShape.mk.injEq] at hshape
  exact ⟨hshape.1.trans hr, hshape.2.trans hw, muldersStorjohannStep_wellFormed shift hM,
    muldersStorjohannStep_shiftedDegreeLe hM hD i j⟩

/-! ## The shift of a cancellation -/

omit [DecidableEq F] in
/-- **The shift of a cancellation fits in the bound**: cancelling the target's leading term
(shifted degree `t.shiftedDegree`) by `c·X^d·b`, `d = t.degree − r.degree`, every nonzero entry
`b_j` of the reducer has `d + |b_j| ≤ t.shiftedDegree + 1`: the fused update writes arrays of at
most `t.shiftedDegree + 1` coefficients. -/
theorem cancel_shift_add_size_le {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position) (hle : r.shiftedDegree ≤ t.shiftedDegree)
    {j : ℕ} (hj : j < reducer.size) (hne : rowGet reducer j ≠ 0) :
    (t.degree - r.degree) + (rowGet reducer j).val.size ≤ t.shiftedDegree + 1 := by
  obtain ⟨-, -, -, -, ht5, -⟩ := rowShiftedLeadingTerm?_some_data ht
  obtain ⟨-, -, -, -, hr5, -⟩ := rowShiftedLeadingTerm?_some_data hr
  have hb := rowShiftedLeadingTerm?_entry_bound hr hj hne
  have := val_size_le_natDegree_add_one (rowGet reducer j)
  rw [hpos] at ht5
  omega

omit [DecidableEq F] in
/-- The degree of the target's leading entry is at most its shifted degree, so the shift `d` of
a cancellation is at most the bound. -/
theorem cancel_shift_le {target : PolynomialRow F} {shift : Array Nat}
    {t : ShiftedLeadingTerm F} (ht : rowShiftedLeadingTerm? target shift = some t) :
    t.degree ≤ t.shiftedDegree := by
  obtain ⟨-, -, -, -, ht5, -⟩ := rowShiftedLeadingTerm?_some_data ht
  omega

/-! ## The number of steps -/

/-- **The number of steps** the fast loop makes (`muldersStorjohannReduceWithFuelFast`'s
recursion, counting the steps taken). -/
@[expose] def msStepCount : ℕ → PolynomialMatrix F → Array Nat → ℕ
  | 0, _M, _shift => 0
  | fuel + 1, M, shift =>
    match cachedLeadingConflict? (rowLeadingPositions M shift) with
    | none => 0
    | some (i, j) => msStepCount fuel (muldersStorjohannStepFast M shift i j) shift + 1

/-- A step of the fast loop decreases CompPoly's measure. -/
theorem stepFast_measure_lt {M : PolynomialMatrix F} {shift : Array Nat} {i j : ℕ}
    (hM : WellFormed M) (hc : cachedLeadingConflict? (rowLeadingPositions M shift) = some (i, j)) :
    shiftedMatrixMeasure (muldersStorjohannStepFast M shift i j) shift <
      shiftedMatrixMeasure M shift := by
  rw [cachedLeadingConflict?_eq] at hc
  rw [muldersStorjohannStepFast_eq]
  exact muldersStorjohannStep_shiftedMatrixMeasure_lt hM hc

/-- **At most the measure many steps.** -/
theorem msStepCount_le_measure (fuel : ℕ) :
    ∀ (M : PolynomialMatrix F) (shift : Array Nat), WellFormed M →
      msStepCount fuel M shift ≤ shiftedMatrixMeasure M shift := by
  induction fuel with
  | zero => intro M shift _; simp [msStepCount]
  | succ fuel ih =>
    intro M shift hM
    rw [msStepCount]
    split
    · omega
    · rename_i i j hc
      have hlt := stepFast_measure_lt hM hc
      have := ih (muldersStorjohannStepFast M shift i j) shift
        (by rw [muldersStorjohannStepFast_eq]; exact muldersStorjohannStep_wellFormed shift hM)
      omega

omit [DecidableEq F] in
/-- **The measure is at most `r·(D + 1)·(w + 1)`.** -/
theorem shiftedMatrixMeasure_le_of_shiftedDegreeLe {M : PolynomialMatrix F}
    {shift : Array Nat} {D : ℕ} (hM : WellFormed M) (h : ShiftedDegreeLe M shift D) :
    shiftedMatrixMeasure M shift ≤ M.size * ((D + 1) * (MatrixWidth M + 1)) := by
  refine shiftedMatrixMeasure_le_of_degree_bound hM fun i d hi hd ↦ ?_
  exact rowShiftedDegree?_le_of_entry_bound (fun k _ hk ↦ h i hi k hk) hd

/-- **The number of steps of Mulders–Storjohann**: on `r` rows of width `w` whose entries have
shifted degrees at most `D`, the loop makes at most `r·(D + 1)·(w + 1)` steps, whatever the fuel. -/
theorem msStepCount_le {r w D : ℕ} {M : PolynomialMatrix F} {shift : Array Nat}
    (h : MsInv r w D M shift) (fuel : ℕ) :
    msStepCount fuel M shift ≤ r * ((D + 1) * (w + 1)) := by
  obtain ⟨hr, hw, hM, hD⟩ := h
  have := shiftedMatrixMeasure_le_of_shiftedDegreeLe hM hD
  rw [hr, hw] at this
  exact (msStepCount_le_measure fuel M shift hM).trans this

/-! ## A cost recurrence, solved -/

/-- **Any cost of the loop paying at most `c` per iteration is at most `(measure + 1)·c`**: if
`T fuel M` is at most `c` when the fuel is out, and at most `c` plus the cost of the rest of the
loop otherwise, on every matrix satisfying the invariant, then `T fuel M ≤ (measure M + 1)·c`. -/
theorem msLoop_cost_le_measure {r w D c : ℕ} {shift : Array Nat}
    (T : ℕ → PolynomialMatrix F → ℕ)
    (h0 : ∀ M, MsInv r w D M shift → T 0 M ≤ c)
    (hstep : ∀ fuel M, MsInv r w D M shift →
      T (fuel + 1) M ≤ c +
        match cachedLeadingConflict? (rowLeadingPositions M shift) with
        | none => 0
        | some (i, j) => T fuel (muldersStorjohannStepFast M shift i j)) :
    ∀ fuel M, MsInv r w D M shift → T fuel M ≤ (shiftedMatrixMeasure M shift + 1) * c := by
  intro fuel
  induction fuel with
  | zero => intro M hM; have := h0 M hM; nlinarith
  | succ fuel ih =>
    intro M hM
    have hs := hstep fuel M hM
    split at hs
    · nlinarith
    · rename_i i j hc
      have hlt := stepFast_measure_lt hM.2.2.1 hc
      have hrest := ih _ (muldersStorjohannStepFast_msInv hM i j)
      have : (shiftedMatrixMeasure (muldersStorjohannStepFast M shift i j) shift + 1) * c ≤
          shiftedMatrixMeasure M shift * c := Nat.mul_le_mul_right c hlt
      nlinarith

/-- **The loop's cost in closed form**: `T fuel M ≤ (r·(D + 1)·(w + 1) + 1)·c`. -/
theorem msLoop_cost_le {r w D c : ℕ} {shift : Array Nat}
    (T : ℕ → PolynomialMatrix F → ℕ)
    (h0 : ∀ M, MsInv r w D M shift → T 0 M ≤ c)
    (hstep : ∀ fuel M, MsInv r w D M shift →
      T (fuel + 1) M ≤ c +
        match cachedLeadingConflict? (rowLeadingPositions M shift) with
        | none => 0
        | some (i, j) => T fuel (muldersStorjohannStepFast M shift i j))
    (fuel : ℕ) {M : PolynomialMatrix F} (hM : MsInv r w D M shift) :
    T fuel M ≤ (r * ((D + 1) * (w + 1)) + 1) * c := by
  refine (msLoop_cost_le_measure T h0 hstep fuel M hM).trans (Nat.mul_le_mul_right c ?_)
  obtain ⟨hr, hw, hW, hD⟩ := hM
  have := shiftedMatrixMeasure_le_of_shiftedDegreeLe hW hD
  rw [hr, hw] at this
  omega

/-! ## Lee–O'Sullivan's initial basis

Row `i ≤ ℓ` of Lee–O'Sullivan's basis is the bivariate polynomial
`P_i = Y^(i−t)·(Y − R)^t·G^(m−t)`, `t = min i m`, as its `Y`-coefficients: entry `j` is the
coefficient of `Y^j`, a polynomial in `X`. With `deg R, deg G ≤ n`, every entry has `X`-degree at
most `t·deg R + (m−t)·deg G ≤ m·n` (`XDegLe`: products add the bounds), and is zero for `j > i`;
the shift of column `j` is `j·(k−1)`, so every shifted degree is at most `m·n + ℓ·(k−1)`
(`leeOSullivanBasis_msInv`). -/

open Polynomial CompPoly.GuruswamiSudan

/-- Every `Y`-coefficient of a polynomial in `F[X][Y]` has `X`-degree at most `d`. -/
@[expose] def XDegLe (P : Polynomial (Polynomial F)) (d : ℕ) : Prop := ∀ j, (P.coeff j).natDegree ≤ d

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem XDegLe.mono {P : Polynomial (Polynomial F)} {a b : ℕ} (h : XDegLe P a) (hab : a ≤ b) :
    XDegLe P b := fun j ↦ (h j).trans hab

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem XDegLe.mul {P Q : Polynomial (Polynomial F)} {a b : ℕ} (hP : XDegLe P a)
    (hQ : XDegLe Q b) : XDegLe (P * Q) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ ↦ ?_
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hP _) (hQ _))

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem XDegLe.one : XDegLe (1 : Polynomial (Polynomial F)) 0 := by
  intro j
  rw [Polynomial.coeff_one]
  split <;> simp

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem XDegLe.pow {P : Polynomial (Polynomial F)} {a : ℕ} (hP : XDegLe P a) (e : ℕ) :
    XDegLe (P ^ e) (e * a) := by
  induction e with
  | zero => simpa using XDegLe.one
  | succ e ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hP

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem XDegLe.X : XDegLe (Polynomial.X : Polynomial (Polynomial F)) 0 := by
  intro j
  rw [Polynomial.coeff_X]
  split <;> simp

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem XDegLe.C (p : Polynomial F) : XDegLe (Polynomial.C p) p.natDegree := by
  intro j
  rw [Polynomial.coeff_C]
  split <;> simp

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem XDegLe.X_sub_C (p : Polynomial F) : XDegLe (Polynomial.X - Polynomial.C p) p.natDegree := by
  intro j
  rw [Polynomial.coeff_sub]
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (XDegLe.C p j))
  exact (XDegLe.X j).trans (Nat.zero_le _)

/-- `CBivariate.toPoly` as the ring equivalence. -/
theorem cbivariate_toPoly_eq (Q : CBivariate F) :
    CBivariate.toPoly Q = CBivariate.ringEquiv Q := rfl

omit [DecidableEq F] in
theorem toPoly_ofYConstant (G : CPolynomial F) :
    CBivariate.toPoly (CBivariate.ofYConstant G) = Polynomial.C G.toPoly := by
  rw [CBivariate.toPoly_eq_map]
  show (CPolynomial.toPoly (CPolynomial.C G : CPolynomial (CPolynomial F))).map _ = _
  rw [CPolynomial.C_toPoly, Polynomial.map_C, RingEquiv.coe_toRingHom, CPolynomial.ringEquiv_apply]

theorem toPoly_linearYDivisor (R : CPolynomial F) :
    CBivariate.toPoly (CBivariate.linearYDivisor R) = Polynomial.X - Polynomial.C R.toPoly := by
  rw [CBivariate.toPoly_eq_map, CBivariate.linearYDivisor_toPoly, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, RingEquiv.coe_toRingHom, CPolynomial.ringEquiv_apply]

theorem toPoly_leeOSullivanBasisPolynomial (R G : CPolynomial F) (params : GSInterpParams)
    (i : ℕ) :
    CBivariate.toPoly (GuruswamiSudan.leeOSullivanBasisPolynomial R G params i) =
      Polynomial.X ^ (i - GuruswamiSudan.leeOSullivanT params i) *
        (Polynomial.X - Polynomial.C R.toPoly) ^ GuruswamiSudan.leeOSullivanT params i *
          (Polynomial.C G.toPoly) ^ (params.multiplicity - GuruswamiSudan.leeOSullivanT params i) := by
  rw [GuruswamiSudan.leeOSullivanBasisPolynomial, cbivariate_toPoly_eq, map_mul, map_mul, map_pow,
    map_pow, map_pow, ← cbivariate_toPoly_eq, ← cbivariate_toPoly_eq, ← cbivariate_toPoly_eq,
    CBivariate.Y_toPoly, toPoly_linearYDivisor, toPoly_ofYConstant]

/-- **The entries of Lee–O'Sullivan's basis polynomials**: every `Y`-coefficient of `P_i` has
`X`-degree at most `m·n` when `deg R, deg G ≤ n`. -/
theorem natDegree_coeff_leeOSullivanBasisPolynomial (R G : CPolynomial F)
    (params : GSInterpParams) {n : ℕ} (hR : R.natDegree ≤ n) (hG : G.natDegree ≤ n) (i j : ℕ) :
    (CPolynomial.coeff (GuruswamiSudan.leeOSullivanBasisPolynomial R G params i) j).natDegree ≤
      params.multiplicity * n := by
  set t := GuruswamiSudan.leeOSullivanT params i
  have ht : t ≤ params.multiplicity := min_le_right _ _
  have h := ((XDegLe.X.pow (i - t)).mul ((XDegLe.X_sub_C R.toPoly).pow t)).mul
    ((XDegLe.C G.toPoly).pow (params.multiplicity - t)) j
  rw [← toPoly_leeOSullivanBasisPolynomial, CBivariate.toPoly_coeff,
    ← CPolynomial.natDegree_toPoly, ← CPolynomial.natDegree_toPoly, ← CPolynomial.natDegree_toPoly] at h
  refine h.trans ?_
  have h1 : t * R.natDegree ≤ t * n := Nat.mul_le_mul_left t hR
  have h2 : (params.multiplicity - t) * G.natDegree ≤ (params.multiplicity - t) * n :=
    Nat.mul_le_mul_left _ hG
  have h3 : t * n + (params.multiplicity - t) * n = params.multiplicity * n := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' ht]
  omega

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem weightedDegreeShift_getD (w width j : ℕ) (hj : j < width) :
    (CBivariate.weightedDegreeShift w width).getD j 0 = j * w := by
  simp [CBivariate.weightedDegreeShift, Array.getD_eq_getD_getElem?, hj]

/-- **Lee–O'Sullivan's initial basis satisfies the invariant**: `ℓ + 1` rows of width `ℓ + 1`
(`ℓ = interpolationYCap`), every shifted degree at most `m·n + ℓ·(k − 1)`, when
`deg R, deg G ≤ n`. -/
theorem leeOSullivanBasis_msInv (R G : CPolynomial F) (params : GSInterpParams) {n : ℕ}
    (hR : R.natDegree ≤ n) (hG : G.natDegree ≤ n) :
    MsInv (GuruswamiSudan.interpolationYCap params + 1) (GuruswamiSudan.interpolationYCap params + 1)
      (params.multiplicity * n +
        GuruswamiSudan.interpolationYCap params * GuruswamiSudan.yWeight params)
      (GuruswamiSudan.leeOSullivanBasisRowsWithRG R G params)
      (GuruswamiSudan.leeOSullivanShifts params) := by
  have hsize : (GuruswamiSudan.leeOSullivanBasisRowsWithRG R G params).size =
      GuruswamiSudan.leeOSullivanWidth params := by
    simp [GuruswamiSudan.leeOSullivanBasisRowsWithRG]
  refine ⟨hsize, GuruswamiSudan.LeeOSullivan.leeOSullivanBasisRowsWithRG_width R G params,
    GuruswamiSudan.LeeOSullivan.leeOSullivanBasisRowsWithRG_wellFormed R G params, ?_⟩
  intro i hi j hj
  rw [hsize] at hi
  have hjw : j < GuruswamiSudan.leeOSullivanWidth params := by
    by_contra hge
    apply hj
    apply rowGet_eq_zero_of_size_le
    rw [matrix_getD_size_of_wellFormed
      (GuruswamiSudan.LeeOSullivan.leeOSullivanBasisRowsWithRG_wellFormed R G params)
      (by rw [hsize]; exact hi),
      GuruswamiSudan.LeeOSullivan.leeOSullivanBasisRowsWithRG_width]
    omega
  rw [GuruswamiSudan.LeeOSullivan.rowGet_leeOSullivanBasisRowsWithRG_getD R G params hi hjw] at hj ⊢
  have hji : j ≤ i := by
    by_contra hlt
    exact hj (GuruswamiSudan.LeeOSullivan.leeOSullivanBasisPolynomial_coeffY_eq_zero_of_idx_lt
      R G params (by omega))
  rw [GuruswamiSudan.leeOSullivanShifts, weightedDegreeShift_getD _ _ _ hjw]
  have hdeg := natDegree_coeff_leeOSullivanBasisPolynomial R G params hR hG i j
  have hiw : i ≤ GuruswamiSudan.interpolationYCap params := by
    simp only [GuruswamiSudan.leeOSullivanWidth] at hi; omega
  have := Nat.mul_le_mul_right (GuruswamiSudan.yWeight params) (hji.trans hiw)
  omega

/-! ## The degrees of `G` and `R` -/

omit [DecidableEq F] in
theorem natDegree_one_cpoly : (1 : CPolynomial F).natDegree = 0 := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_one, Polynomial.natDegree_one]

omit [DecidableEq F] in
theorem natDegree_linearFactor (x : F) : (CPolynomial.linearFactor x).natDegree ≤ 1 := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.linearFactor, CPolynomial.toPoly_add,
    CPolynomial.C_toPoly, CPolynomial.X_toPoly]
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (by simp) Polynomial.natDegree_X_le)

omit [DecidableEq F] in
theorem natDegree_foldl_linearFactor (l : List F) (acc : CPolynomial F) :
    (l.foldl (fun acc x ↦ acc * CPolynomial.linearFactor x) acc).natDegree ≤
      acc.natDegree + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, List.length_cons]
    have := (CPolynomial.natDegree_mul_le acc (CPolynomial.linearFactor x)).trans
      (Nat.add_le_add_left (natDegree_linearFactor x) _)
    have := ih (acc * CPolynomial.linearFactor x)
    omega

omit [DecidableEq F] in
/-- **The vanishing polynomial of `n` points has degree at most `n`.** -/
theorem natDegree_vanishingPolynomialArray (xs : Array F) :
    (CPolynomial.vanishingPolynomialArray xs).natDegree ≤ xs.size := by
  rw [CPolynomial.vanishingPolynomialArray, ← Array.foldl_toList]
  have := natDegree_foldl_linearFactor xs.toList 1
  rw [natDegree_one_cpoly, Array.length_toList] at this
  omega

omit [DecidableEq F] in
theorem natDegree_divByLinearFactor_le (p : CPolynomial F) (x : F) :
    (CPolynomial.divByLinearFactor p x).natDegree ≤ p.natDegree := by
  have hmonic : (CPolynomial.linearFactor x).monic := by
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.linearFactor, CPolynomial.toPoly_add,
      CPolynomial.C_toPoly, CPolynomial.X_toPoly, add_comm]
    exact Polynomial.monic_X_add_C _
  rw [CPolynomial.divByLinearFactor_eq_divByMonic, CPolynomial.natDegree_toPoly,
    CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ hmonic, Polynomial.natDegree_divByMonic _ ((CPolynomial.monic_toPoly_iff _).1 hmonic),
    ← CPolynomial.natDegree_toPoly]
  omega

/-- **The interpolation polynomial `R` has degree at most `deg G`.** -/
theorem natDegree_interpolateCoefficientFormWithVanishing (E : CPolynomial.BatchEvalContext F)
    (G : CPolynomial F) (points : Array (F × F)) :
    (CPolynomial.interpolateCoefficientFormWithVanishing E G points).natDegree ≤ G.natDegree := by
  rw [CPolynomial.interpolateCoefficientFormWithVanishing]
  generalize (E.evalBatchWith _ _) = dv
  have h : ∀ (l : List ℕ) (acc : CPolynomial F), acc.natDegree ≤ G.natDegree →
      (l.foldl (fun acc i ↦ acc + CPolynomial.interpolationTermWithVanishing G
        (points.getD i (0, 0)) (dv.getD i 0)) acc).natDegree ≤ G.natDegree := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons i l ih =>
      intro acc hacc
      refine ih _ ((CPolynomial.natDegree_add_le _ _).trans (max_le hacc ?_))
      rw [CPolynomial.interpolationTermWithVanishing]
      refine (CPolynomial.natDegree_mul_le _ _).trans ?_
      rw [CPolynomial.natDegree_C, Nat.zero_add]
      exact natDegree_divByLinearFactor_le G _
  exact h _ 0 (by rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero]; simp)

/-- **Lee–O'Sullivan's basis on `n` points satisfies the invariant**: `ℓ + 1` rows of width
`ℓ + 1`, shifted degrees at most `m·n + ℓ·(k − 1)`. -/
theorem leeOSullivanBasisRows_msInv (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F) (points : Array (F × F)) (params : GSInterpParams) :
    MsInv (interpolationYCap params + 1) (interpolationYCap params + 1)
      (params.multiplicity * points.size + interpolationYCap params * yWeight params)
      (leeOSullivanBasisRows V E points params) (leeOSullivanShifts params) := by
  have hG : (V.vanishingPolynomial (points.map fun point ↦ point.1)).natDegree ≤ points.size := by
    rw [V.correct]
    simpa using natDegree_vanishingPolynomialArray (points.map fun point ↦ point.1)
  exact leeOSullivanBasis_msInv _ _ params
    ((natDegree_interpolateCoefficientFormWithVanishing E _ points).trans hG) hG

/-! ## At the extractor's parameters -/

open LeanVM.Parameters LeanVM.Extraction

/-- The Lee–O'Sullivan basis of lane `u` at the decoder's parameters (`gsLaneAtFast`'s
interpolation: `interpContext`, the direct vanishing polynomial and Horner's evaluations). -/
@[expose] def laneBasis (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : PolynomialMatrix K :=
  leeOSullivanBasisRows CPolynomial.VanishingPolynomialContext.direct
    (CPolynomial.BatchEvalContext.horner K) (lanePoints (2 ^ (κ + R)) W u)
    (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp

/-- The `Y`-degree bound `ℓ = ⌊W/(k − 1)⌋` of the decoder's parameters. -/
@[expose] def laneYCap (κ R A : ℕ) : ℕ := interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp

/-- The multiplicity `m` of the decoder's parameters. -/
@[expose] def laneMult (κ R A : ℕ) : ℕ := gsMultiplicityAt (2 ^ κ) (2 ^ (κ + R)) A

/-- The degree bound `D = m·n + ℓ·(k − 1)` of the lane's basis. -/
@[expose] def laneDegBound (κ R A : ℕ) : ℕ :=
  laneMult κ R A * 2 ^ (κ + R) + laneYCap κ R A * (2 ^ κ - 1)

/-- **The lane's basis satisfies the invariant**: `ℓ + 1` rows of width `ℓ + 1`, every shifted
degree at most `D = m·n + ℓ·(k − 1)`. -/
theorem laneBasis_msInv (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) :
    MsInv (laneYCap κ R A + 1) (laneYCap κ R A + 1) (laneDegBound κ R A) (laneBasis κ R A W u)
      (leeOSullivanShifts (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp) := by
  have h := leeOSullivanBasisRows_msInv CPolynomial.VanishingPolynomialContext.direct
    (CPolynomial.BatchEvalContext.horner K) (lanePoints (2 ^ (κ + R)) W u)
    (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp
  rwa [show (lanePoints (2 ^ (κ + R)) W u).size = 2 ^ (κ + R) by simp [lanePoints]] at h

/-- **The number of Mulders–Storjohann steps on a lane**: the reduction the decoder runs
(`muldersStorjohannReduceFast`, fuel `muldersStorjohannFuel`) makes at most
`(ℓ + 1)·(D + 1)·(ℓ + 2)` steps, `D = m·n + ℓ·(k − 1)`. -/
theorem laneStepCount_le (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) :
    msStepCount
        (muldersStorjohannFuel (laneBasis κ R A W u)
          (leeOSullivanShifts (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp))
        (laneBasis κ R A W u) (leeOSullivanShifts (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp) ≤
      (laneYCap κ R A + 1) * ((laneDegBound κ R A + 1) * (laneYCap κ R A + 2)) :=
  msStepCount_le (laneBasis_msInv κ R A W u) _

/-- The degree bound in the parameters: `D ≤ m·n + W`, `W = m·A − 1` the weighted degree. -/
theorem laneDegBound_le (κ R A : ℕ) :
    laneDegBound κ R A ≤ laneMult κ R A * 2 ^ (κ + R) + (laneMult κ R A * A - 1) := by
  unfold laneDegBound laneYCap laneMult
  simp only [interpolationYCap, yWeight, gsParamsFor, gsParamsAt]
  have := Nat.div_mul_le_self (gsMultiplicityAt (2 ^ κ) (2 ^ (κ + R)) A * A - 1) (2 ^ κ - 1)
  omega

end

end LeanVM.Cost.Bounds
