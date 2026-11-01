module

public import LeanVM.Cost.Bounds.MuldersStorjohann
public import LeanVM.Cost.Bounds.Sizes.Lane
public import LeanVM.Protocol.Extraction.Fast.LeeRows
import all CompPoly.Univariate.Basic

/-!
# Sizes along the decoder: the interpolation

The sizes of the lane interpolation's values (`interpolateDistinct`, `Fast/DecoderFast.lean`:
Lee–O'Sullivan with `vanishingFast`, Horner's evaluations, `leeRowsFast`, CompPoly's
Mulders–Storjohann and `normalizeLeeFast`), on `n` points at the parameters `k`, `m`, `W`,
`ℓ = ⌊W/(k − 1)⌋`:

* the vanishing polynomial `G` has degree at most `n`, so at most `n + 1` coefficients
  (`vanishingFast_natDegree_le`, `vanishingFast_size_le`); the interpolating polynomial `R` degree
  at most `deg G − 1`, so at most `max 1 n` coefficients (`interpolate_natDegree_le_pred`,
  `interpolate_size_le`);
* `leeRowsFast`'s powers: `(Y − R)^i` has `i + 1` rows of at most `i·deg R + 1` coefficients,
  `G^j` one row of at most `j·deg G + 1` (`linearYDivisor_pow_sizes`, `ofYConstant_pow_sizes`);
  its rows satisfy Mulders–Storjohann's invariant (`leeRowsFast_msInv`, `interpBasis_msInv`):
  `ℓ + 1` rows of width `ℓ + 1`, every shifted degree at most `D = m·n + ℓ·(k − 1)`, so entries of
  at most `D + 1` coefficients; the reduced matrix keeps it (`muldersStorjohannReduceFast_msInv`);
* `normalizeLeeFast`'s output: at most `min (W + 1) |Q|` rows, row `y` of at most
  `W + 1 − (k − 1)·y` coefficients (`leeScaled_size_le`, `leeScaled_row_size_le`);
* the interpolated `Q` (on distinct points, `k > 1`): at most `ℓ + 1` rows, row `y` of at most
  `W + 1 − (k − 1)·y` coefficients (`interpolateDistinct_sizes`).
-/

namespace LeanVM.Cost.Bounds

open CompPoly CompPoly.GuruswamiSudan CompPoly.PolynomialMatrix LeanVM.Extraction.Fast
open LeanVM.Extraction LeanVM.Parameters

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-! ## The vanishing and interpolating polynomials -/

theorem cpoly_size_le_natDegree {R : Type*} [Zero R] (p : CPolynomial R) :
    p.val.size ≤ p.natDegree + 1 := by
  unfold CPolynomial.natDegree
  split <;> omega

omit [DecidableEq F] in
theorem vanishingFast_natDegree_le (xs : Array F) : (vanishingFast xs).natDegree ≤ xs.size := by
  rw [vanishingFast_eq]; exact natDegree_vanishingPolynomialArray xs

omit [DecidableEq F] in
/-- **The vanishing polynomial of `n` points has at most `n + 1` coefficients.** -/
theorem vanishingFast_size_le (xs : Array F) : (vanishingFast xs).val.size ≤ xs.size + 1 :=
  (val_size_le_natDegree_add_one _).trans (Nat.add_le_add_right (vanishingFast_natDegree_le xs) 1)

omit [DecidableEq F] in
theorem natDegree_divByLinearFactor_le_pred (p : CPolynomial F) (x : F) :
    (CPolynomial.divByLinearFactor p x).natDegree ≤ p.natDegree - 1 := by
  have htp : (CPolynomial.linearFactor x).toPoly = Polynomial.X + Polynomial.C (-x) := by
    rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.C_toPoly,
      CPolynomial.X_toPoly, add_comm]
  have hmonic : (CPolynomial.linearFactor x).monic := by
    rw [CPolynomial.monic_toPoly_iff, htp]
    exact Polynomial.monic_X_add_C _
  rw [CPolynomial.divByLinearFactor_eq_divByMonic, CPolynomial.natDegree_toPoly,
    CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ hmonic,
    Polynomial.natDegree_divByMonic _ ((CPolynomial.monic_toPoly_iff _).1 hmonic), htp,
    Polynomial.natDegree_X_add_C, ← CPolynomial.natDegree_toPoly]

/-- **The interpolating polynomial has degree at most `deg G − 1`.** -/
theorem interpolate_natDegree_le_pred (E : CPolynomial.BatchEvalContext F) (G : CPolynomial F)
    (points : Array (F × F)) :
    (CPolynomial.interpolateCoefficientFormWithVanishing E G points).natDegree ≤
      G.natDegree - 1 := by
  rw [CPolynomial.interpolateCoefficientFormWithVanishing]
  generalize (E.evalBatchWith _ _) = dv
  have h : ∀ (l : List ℕ) (acc : CPolynomial F), acc.natDegree ≤ G.natDegree - 1 →
      (l.foldl (fun acc i ↦ acc + CPolynomial.interpolationTermWithVanishing G
        (points.getD i (0, 0)) (dv.getD i 0)) acc).natDegree ≤ G.natDegree - 1 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons i l ih =>
      intro acc hacc
      refine ih _ ((CPolynomial.natDegree_add_le _ _).trans (max_le hacc ?_))
      rw [CPolynomial.interpolationTermWithVanishing]
      refine (CPolynomial.natDegree_mul_le _ _).trans ?_
      rw [CPolynomial.natDegree_C, Nat.zero_add]
      exact natDegree_divByLinearFactor_le_pred G _
  exact h _ 0 (by rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero]; simp)

/-- **The interpolating polynomial of `n` points has at most `max 1 n` coefficients.** -/
theorem interpolate_size_le (E : CPolynomial.BatchEvalContext F) (points : Array (F × F)) :
    (CPolynomial.interpolateCoefficientFormWithVanishing E
      (vanishingFast (points.map fun p ↦ p.1)) points).val.size ≤ max 1 points.size := by
  have h1 := interpolate_natDegree_le_pred E (vanishingFast (points.map fun p ↦ p.1)) points
  have h2 := vanishingFast_natDegree_le (points.map fun p ↦ p.1)
  have h3 := val_size_le_natDegree_add_one
    (CPolynomial.interpolateCoefficientFormWithVanishing E
      (vanishingFast (points.map fun p ↦ p.1)) points)
  simp only [Array.size_map] at h2
  omega

/-! ## Lee–O'Sullivan's rows -/

omit [DecidableEq F] in
/-- An entry bound for a bivariate polynomial from its image in `F[X][Y]`. -/
theorem row_size_le_of_xDegLe {P : CBivariate F} {d : ℕ} (h : XDegLe (CBivariate.toPoly P) d)
    (j : ℕ) : (P.val.coeff j).val.size ≤ d + 1 := by
  have h1 := h j
  rw [CBivariate.toPoly_coeff, ← CPolynomial.natDegree_toPoly] at h1
  exact (val_size_le_natDegree_add_one _).trans (Nat.add_le_add_right h1 1)

/-- **`(Y − R)^i`**: at most `i + 1` rows, each of at most `i·deg R + 1` coefficients. -/
theorem linearYDivisor_pow_sizes (R : CPolynomial F) (i : ℕ) :
    (CBivariate.linearYDivisor R ^ i).val.size ≤ i + 1 ∧
      ∀ j, ((CBivariate.linearYDivisor R ^ i).val.coeff j).val.size ≤ i * R.natDegree + 1 := by
  refine ⟨?_, fun j ↦ row_size_le_of_xDegLe ?_ j⟩
  · refine (cpoly_size_le_natDegree _).trans (Nat.add_le_add_right ?_ 1)
    rw [CPolynomial.natDegree_toPoly]
    have hp := CPolynomial.toPoly_pow (CBivariate.linearYDivisor R : CBivariate F) i
    change CPolynomial.toPoly ((CBivariate.linearYDivisor R : CBivariate F) ^ i) =
      CPolynomial.toPoly (CBivariate.linearYDivisor R : CBivariate F) ^ i at hp
    rw [hp, CBivariate.linearYDivisor_toPoly]
    exact Polynomial.natDegree_pow_le.trans (by rw [Polynomial.natDegree_X_sub_C, Nat.mul_one])
  · rw [cbivariate_toPoly_eq, map_pow, ← cbivariate_toPoly_eq, toPoly_linearYDivisor,
      CPolynomial.natDegree_toPoly]
    exact (XDegLe.X_sub_C _).pow i

/-- **`G^j`**: one row of at most `j·deg G + 1` coefficients. -/
theorem ofYConstant_pow_sizes (G : CPolynomial F) (j : ℕ) :
    (CBivariate.ofYConstant G ^ j).val.size ≤ 1 ∧
      ∀ y, ((CBivariate.ofYConstant G ^ j).val.coeff y).val.size ≤ j * G.natDegree + 1 := by
  refine ⟨?_, fun y ↦ row_size_le_of_xDegLe ?_ y⟩
  · refine (cpoly_size_le_natDegree _).trans (Nat.add_le_add_right ?_ 1)
    rw [CPolynomial.natDegree_toPoly]
    have hp := CPolynomial.toPoly_pow (CBivariate.ofYConstant G : CBivariate F) j
    change CPolynomial.toPoly ((CBivariate.ofYConstant G : CBivariate F) ^ j) =
      CPolynomial.toPoly (CBivariate.ofYConstant G : CBivariate F) ^ j at hp
    rw [hp]
    show (CPolynomial.toPoly (CPolynomial.C G : CPolynomial (CPolynomial F)) ^ j).natDegree ≤ 0
    rw [CPolynomial.C_toPoly, ← Polynomial.C_pow, Polynomial.natDegree_C]
  · rw [cbivariate_toPoly_eq, map_pow, ← cbivariate_toPoly_eq, toPoly_ofYConstant,
      CPolynomial.natDegree_toPoly]
    exact (XDegLe.C _).pow j

/-- **`leeRowsFast`'s rows satisfy Mulders–Storjohann's invariant.** -/
theorem leeRowsFast_msInv (R G : CPolynomial F) (params : GSInterpParams) {n : ℕ}
    (hR : R.natDegree ≤ n) (hG : G.natDegree ≤ n) :
    MsInv (interpolationYCap params + 1) (interpolationYCap params + 1)
      (params.multiplicity * n + interpolationYCap params * yWeight params)
      (leeRowsFast R G params) (leeOSullivanShifts params) := by
  rw [leeRowsFast_eq]
  exact leeOSullivanBasis_msInv R G params hR hG

/-- **The interpolation's basis on `n` points**: `ℓ + 1` rows of width `ℓ + 1`, every shifted
degree at most `m·n + ℓ·(k − 1)`. -/
theorem interpBasis_msInv (E : CPolynomial.BatchEvalContext F) (points : Array (F × F))
    (params : GSInterpParams) :
    MsInv (interpolationYCap params + 1) (interpolationYCap params + 1)
      (params.multiplicity * points.size + interpolationYCap params * yWeight params)
      (leeRowsFast (CPolynomial.interpolateCoefficientFormWithVanishing E
        (vanishingFast (points.map fun p ↦ p.1)) points)
        (vanishingFast (points.map fun p ↦ p.1)) params) (leeOSullivanShifts params) := by
  have hG := vanishingFast_natDegree_le (points.map fun p ↦ p.1)
  simp only [Array.size_map] at hG
  exact leeRowsFast_msInv _ _ params
    ((natDegree_interpolateCoefficientFormWithVanishing E _ points).trans hG) hG

/-- **Mulders–Storjohann keeps the invariant**: the reduced matrix too. -/
theorem muldersStorjohannReduceWithFuelFast_msInv {r w D : ℕ} {shift : Array Nat} (fuel : ℕ) :
    ∀ {M : PolynomialMatrix F}, MsInv r w D M shift →
      MsInv r w D (muldersStorjohannReduceWithFuelFast fuel M shift) shift := by
  induction fuel with
  | zero => intro M h; exact h
  | succ fuel ih =>
    intro M h
    rw [muldersStorjohannReduceWithFuelFast]
    split
    · exact h
    · exact ih (muldersStorjohannStepFast_msInv h _ _)

theorem muldersStorjohannReduceFast_msInv {r w D : ℕ} {shift : Array Nat}
    {M : PolynomialMatrix F} (h : MsInv r w D M shift) :
    MsInv r w D (muldersStorjohannReduceFast M shift) shift :=
  muldersStorjohannReduceWithFuelFast_msInv _ h

/-! ## The normalization -/

omit [DecidableEq F] in
theorem ofFn_size_le {R : Type*} [Zero R] [BEq R] [LawfulBEq R] {n : ℕ} (f : Fin n → R) :
    (CPolynomial.ofFn f).val.size ≤ n :=
  cpoly_val_size_le_of_coeff _ n fun i hi ↦ by
    rw [CPolynomial.coeff_ofFn]
    simp [show ¬ i < n by omega]

omit [DecidableEq F] in
/-- **`normalizeLeeFast`'s output has at most `min (W + 1) |Q|` rows.** -/
theorem leeScaled_size_le (params : GSInterpParams) (Q : CBivariate F) (c : F) :
    (leeScaled params Q c).val.size ≤ leeRows params Q :=
  ofFn_size_le _

omit [DecidableEq F] in
/-- **Row `y` of `normalizeLeeFast`'s output has at most `W + 1 − (k − 1)·y` coefficients.** -/
theorem leeScaled_row_size_le (params : GSInterpParams) (Q : CBivariate F) (c : F) (y : ℕ) :
    ((leeScaled params Q c).val.coeff y).val.size ≤
      params.weightedDegreeBound + 1 - yWeight params * y := by
  refine cpoly_val_size_le_of_coeff _ _ fun i hi ↦ ?_
  show CPolynomial.coeff _ i = 0
  rw [← cbivariate_coeff_eq, coeff_leeScaled]
  split
  · omega
  · rfl

/-! ## The interpolated polynomial -/

/-- **The interpolated `Q`** (distinct points, `k > 1`): at most `ℓ + 1` rows, row `y` of at most
`W + 1 − (k − 1)·y` coefficients. -/
theorem interpolateDistinct_sizes {points : Array (K × K)} (h : DistinctXCoordinates points)
    {params : GSInterpParams} {Q : CBivariate K} (hQ : interpolateDistinct points params = some Q)
    (hk : 1 < params.messageDegree) :
    Q.val.size ≤ interpolationYCap params + 1 ∧
      ∀ y, (Q.val.coeff y).val.size ≤ params.weightedDegreeBound + 1 - yWeight params * y := by
  have hv := interpolateDistinct_valid h hQ
  refine ⟨(lenLe_of_validInterpolation hv hk).1.val_size_le, fun y ↦ ?_⟩
  have hw := (CBivariate.natWeightedDegree_le_iff_coeff Q 1 (yWeight params) _).1 hv.2.1
  refine cpoly_val_size_le_of_coeff _ _ fun i hi ↦ ?_
  by_contra hne
  have := hw i y hne
  omega

end

end LeanVM.Cost.Bounds
