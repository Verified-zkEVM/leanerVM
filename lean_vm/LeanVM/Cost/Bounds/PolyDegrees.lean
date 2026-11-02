module

public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness
public import CompPoly.Bivariate.ToPoly
public import LeanVM.Protocol.Extraction.Extractor
import all CompPoly.Univariate.Basic

/-!
# Polynomial degrees and sizes

A canonical polynomial of degree `d` is an array of at most `d + 1` coefficients
(`val_size_le_natDegree_add_one`); the vanishing polynomial of `n` points has degree at most `n`
(`natDegree_vanishingPolynomialArray`) and the interpolant `R` at most `deg G`
(`natDegree_interpolateCoefficientFormWithVanishing`): the sizes of the lanes' `G` and `R`.
-/

namespace LeanVM.Cost.Bounds

open CompPoly CompPoly.PolynomialMatrix

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- A canonical polynomial of degree `d` is an array of at most `d + 1` coefficients. -/
theorem val_size_le_natDegree_add_one (p : CPolynomial F) : p.val.size ≤ p.natDegree + 1 := by
  unfold CPolynomial.natDegree
  split <;> omega

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

end

end LeanVM.Cost.Bounds
