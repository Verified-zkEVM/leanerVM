/-
  LeanerVM.Protocol.ToCompPoly.SparseEval

  Evaluating a computable multivariate polynomial with each monomial's absent variables skipped.
  Candidate for CompPoly.
-/

module

public import CompPoly.Multivariate.Basic
public import LeanerVM.Protocol.ToCompPoly.FinLoop

/-!
# Sparse evaluation of multivariate polynomials

CompPoly's `CMvPolynomial.eval₂` values a monomial as `∏_{i < n} v_i ^ e_i` over all `n`
variables (`MonoR.evalMonomial`), one power and one product per variable even where the exponent
is zero. A row polynomial of a wide table reads a handful of its `n` columns, so most of that
work multiplies by one. `evalMonomialSparse` skips the variables of exponent zero
(`evalMonomialSparse_eq`), and `eval₂Sparse` is `eval₂` with it; the `@[csimp]` theorem
`eval₂_eq_eval₂Sparse` makes compiled code that names `eval₂` run it. Over an arbitrary
commutative semiring. Nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

open CPoly Std

@[expose] public section

/-- A monomial's value at `vals`, the variables of exponent zero skipped. -/
def evalMonomialSparse {R : Type*} [CommSemiring R] {n : ℕ} (vals : Fin n → R)
    (m : CMvMonomial n) : R :=
  Fin.foldl n (fun acc i ↦ if m.get i = 0 then acc else acc * vals i ^ m.get i) 1

/-- Skipping the variables of exponent zero keeps the monomial's value. -/
theorem evalMonomialSparse_eq {R : Type*} [CommSemiring R] {n : ℕ} (vals : Fin n → R)
    (m : CMvMonomial n) : evalMonomialSparse vals m = MonoR.evalMonomial vals m := by
  have h : (fun acc i ↦ if m.get i = 0 then acc else acc * vals i ^ m.get i) =
      fun (acc : R) i ↦ acc * vals i ^ m.get i := by
    funext acc i
    split <;> simp_all
  rw [evalMonomialSparse, h, MonoR.evalMonomial, ← prodFin_eq_prod, prodFin]

/-- `CMvPolynomial.eval₂` with each monomial valued by `evalMonomialSparse`. -/
def eval₂Sparse {R S : Type*} {n : ℕ} [Semiring R] [CommSemiring S] :
    (R →+* S) → (Fin n → S) → CMvPolynomial n R → S :=
  fun f vs p ↦ ExtTreeMap.foldl (fun s m c ↦ (f c * evalMonomialSparse vs m) + s) 0 p.1

/-- The sparse evaluation is the evaluation. -/
@[csimp] theorem eval₂_eq_eval₂Sparse : @CMvPolynomial.eval₂ = @eval₂Sparse := by
  funext R S n _ _ f vs p
  simp only [CMvPolynomial.eval₂, eval₂Sparse, evalMonomialSparse_eq]

end
end LeanerVM.Protocol
