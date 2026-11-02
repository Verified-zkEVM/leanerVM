module

public import LeanVM.Protocol.Extraction.Fast.EvalMat.Transform
public import CompPoly.Univariate.Lagrange

/-!
# The naive evaluation transform

`EvalTransform.naive pt maxLog`: values at the points `pt v`, `v < 2^j`, one by one, and
Lagrange interpolation back, for `pt` injective below `2^maxLog`. Quadratic: a reference and a
test of the interface, not for the extractor (over `K`, the additive NTT).
-/

namespace LeanVM.Extraction.Fast.EvalMat

open CompPoly

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

namespace EvalTransform

/-- **The naive transform** at the points `pt v`, injective below `2^maxLog`. -/
@[expose] def naive (pt : ℕ → F) (maxLog : ℕ)
    (hpt : ∀ v w, v < 2 ^ maxLog → w < 2 ^ maxLog → pt v = pt w → v = w) : EvalTransform F where
  maxLog := maxLog
  point _ v := pt v
  fwd j p := Array.ofFn fun v : Fin (2 ^ j) ↦ p.eval (pt v)
  inv j y := CPolynomial.CLagrange.interpolate (Finset.univ : Finset (Fin (2 ^ j)))
    (fun v ↦ pt v) (fun v ↦ y.getD v 0)
  size_fwd _ _ _ _ := Array.size_ofFn
  fwd_getD _ _ _ _ v hv := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hv, dite_true, Option.getD_some]
  inv_fwd j p hj hp := by
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.CLagrange.cinterpolate_eq_interpolate]
    have hinj : Set.InjOn (fun v : Fin (2 ^ j) ↦ pt v) ↑(Finset.univ : Finset (Fin (2 ^ j))) :=
      fun v _ w _ h ↦ Fin.ext (hpt v w
        (lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) hj))
        (lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by omega) hj)) h)
    have hdeg : p.toPoly.degree < (Finset.univ : Finset (Fin (2 ^ j))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      rw [← CPolynomial.natDegree_toPoly]
      exact_mod_cast hp
    conv_rhs => rw [Lagrange.eq_interpolate hinj hdeg]
    congr 1
    funext v
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, v.isLt, dite_true,
      Option.getD_some, CPolynomial.eval_toPoly]

end EvalTransform

end

end LeanVM.Extraction.Fast.EvalMat
