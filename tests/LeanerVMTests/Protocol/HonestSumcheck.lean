/-
  LeanerVMTests.Protocol.HonestSumcheck

  Boundary and variable-order controls for honest sumcheck algebra.
-/

module

public import LeanerVM.Protocol.Generic.HonestSumcheckUpstream
import Mathlib.Algebra.Field.ZMod

/-!
# Honest sumcheck controls

A non-symmetric, degree-two polynomial distinguishes high-first binding from low-first binding.
The zero-variable theorem separately covers an empty round schedule.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Protocol MvPolynomial

@[expose] public section

/-- Degree two in variable zero and degree one in variable one. -/
noncomputable def asymmetricPoly : MvPolynomial (Fin 2) ℤ := X 0 ^ 2 + C 3 * X 1

example : MvPolynomial.eval (![5, 2] : Fin 2 → ℤ) asymmetricPoly = 31 := by
  norm_num [asymmetricPoly]

example : MvPolynomial.eval (![2, 5] : Fin 2 → ℤ) asymmetricPoly = 19 := by
  norm_num [asymmetricPoly]

-- Ordered challenges [2,5] bind original variable 1 first, hence terminal value 31.
example : Polynomial.eval 5
    (sumcheckRoundPoly (sumcheckHighFirst asymmetricPoly) 1 (fun _ ↦ (2 : ℤ))) = 31 := by
  have h := sumcheck_highFirst_terminal asymmetricPoly (![2, 5] : Fin 2 → ℤ) (by decide)
  norm_num [asymmetricPoly] at h
  exact h

example (P : MvPolynomial (Fin 0) ℤ) :
    (∑ b : Fin 0 → Fin 2, MvPolynomial.eval (fun i ↦ ((b i).val : ℤ)) P) =
      MvPolynomial.eval Fin.elim0 P := sumcheck_zero_rounds P


-- The first high-first round binds variable one; the low-first round binds variable zero.
example : Polynomial.eval 2
    (sumcheckRoundPoly (sumcheckHighFirst asymmetricPoly) 0 Fin.elim0) = 13 := by
  rw [sumcheck_eval_roundPoly]
  erw [sumcheck_sum_freeCube_suffix (0 : Fin 2)]
  erw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
  norm_num [sumcheckPadSuffix, sumcheckMixPoint, sumcheckHighFirst, asymmetricPoly,
    MvPolynomial.eval_rename, Fin.sum_univ_two, Fin.rev]

example : Polynomial.eval 2 (sumcheckRoundPoly asymmetricPoly 0 Fin.elim0) = 11 := by
  rw [sumcheck_eval_roundPoly]
  erw [sumcheck_sum_freeCube_suffix (0 : Fin 2)]
  erw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
  norm_num [sumcheckPadSuffix, sumcheckMixPoint, asymmetricPoly, Fin.sum_univ_two]

-- The adapter compares polynomials over a finite field, not only their value tables.
example (p : Sumcheck.Spec.OracleStatement (ZMod 2) 2 3 ()) :
    sumcheckRoundPoly p.val 0 Fin.elim0 =
      (Sumcheck.Spec.SingleRound.projectedRoundPolynomial (ZMod 2) 2 3
        (sumcheckBooleanEmbedding (ZMod 2)) 0 Fin.elim0 p).val :=
  sumcheckRoundPoly_eq_projectedRoundPolynomial 0 Fin.elim0 p

-- The original API still accepts a trivial semiring even though the upstream adapter cannot.
example (p : MvPolynomial (Fin 1) (ZMod 1)) :
    Polynomial.eval 0 (sumcheckRoundPoly p 0 Fin.elim0) = MvPolynomial.eval (fun _ ↦ 0) p := by
  have h := sumcheck_roundPoly_terminal p (fun _ ↦ 0) (by decide)
  have hc : (fun _ : Fin 0 ↦ (0 : ZMod 1)) = Fin.elim0 :=
    funext fun i ↦ Fin.elim0 i
  simpa only [hc] using h

example : IsEmpty (Fin 2 ↪ ZMod 1) := sumcheck_no_boolean_embedding (ZMod 1)

example (p : Sumcheck.Spec.OracleStatement ℤ 2 3 ()) (c : Fin 1 → ℤ) :
    (Sumcheck.Spec.SingleRound.projectedRoundPolynomial ℤ 2 3
      (sumcheckBooleanEmbedding ℤ) 1 c p).val.natDegree ≤ degreeOf 1 p.val :=
  projectedRoundPolynomial_natDegree_le (n := 1) (deg := 3)
    (sumcheckBooleanEmbedding ℤ) (1 : Fin 2) c p

end
end LeanerVMTests.Protocol
