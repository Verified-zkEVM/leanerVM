/-
  LeanerVM.Protocol.ToCompPoly.MvEval

  Evaluating a sparse multivariate polynomial by reading only the variables each monomial
  carries, registered for compilation. Candidate for CompPoly.
-/

module

public import CompPoly.Multivariate.Basic
public import LeanerVM.Protocol.ToCompPoly.FinLoop

/-!
# Compiled evaluation of sparse multivariate polynomials

CompPoly's `CMvPolynomial.eval₂` and `CMvPolynomial.eval` value each monomial as
`∏_{i < n} x_i ^ e_i`, a power for each of the `n` variables, though a sparse monomial reads a few
of them. `evalMonomialFast` multiplies only the variables of nonzero exponent, an exponent one
without a power (`evalMonomialFast_eq`); `eval₂Fast` and `evalFast` are `eval₂` and `eval` through
it. Both need their `@[csimp]` theorem: CompPoly compiles `eval` against its own `eval₂`, so a
substitution of `eval₂` does not reach a call that names `eval`. Code compiled after this module
runs the fast versions; no definition changes, and the kernel never sees them. Over an arbitrary
commutative semiring. Nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

open CPoly

@[expose] public section

variable {R : Type*} [CommSemiring R]

/-- A monomial's value, reading only the variables of nonzero exponent. -/
def evalMonomialFast {n : ℕ} (vals : Fin n → R) (m : CMvMonomial n) : R :=
  Fin.foldl n (fun acc i ↦
    let e := m.get i
    if e = 0 then acc else if e = 1 then acc * vals i else acc * vals i ^ e) 1

/-- `evalMonomialFast` is the monomial's value. -/
theorem evalMonomialFast_eq {n : ℕ} (vals : Fin n → R) (m : CMvMonomial n) :
    evalMonomialFast vals m = MonoR.evalMonomial vals m := by
  have h : ∀ (acc : R) (i : Fin n),
      (if m.get i = 0 then acc else if m.get i = 1 then acc * vals i else acc * vals i ^ m.get i) =
        acc * vals i ^ m.get i := fun acc i ↦ by
    split_ifs with h0 h1
    · rw [h0, pow_zero, mul_one]
    · rw [h1, pow_one]
    · rfl
  simp only [evalMonomialFast, h]
  rw [foldl_mul_eq_mul_prod, one_mul]
  rfl

/-- `CMvPolynomial.eval₂` through `evalMonomialFast`. -/
def CMvPolynomial.eval₂Fast {S T : Type*} {n : ℕ} [Semiring S] [CommSemiring T] :
    (S →+* T) → (Fin n → T) → CMvPolynomial n S → T :=
  fun f vs p ↦ Std.ExtTreeMap.foldl (fun s m c ↦ f c * evalMonomialFast vs m + s) 0 p.1

/-- Compiled code evaluates a sparse polynomial through a ring map reading only the variables it
carries. -/
@[csimp] theorem CMvPolynomial.eval₂_eq_eval₂Fast :
    @CMvPolynomial.eval₂ = @CMvPolynomial.eval₂Fast := by
  funext S T n _ _ f vs p
  simp only [CMvPolynomial.eval₂, CMvPolynomial.eval₂Fast, evalMonomialFast_eq]

/-- `CMvPolynomial.eval` through `evalMonomialFast`. -/
def CMvPolynomial.evalFast {S : Type*} {n : ℕ} [CommSemiring S] (vs : Fin n → S)
    (p : CMvPolynomial n S) : S :=
  Std.ExtTreeMap.foldl (fun s m c ↦ c * evalMonomialFast vs m + s) 0 p.1

/-- Compiled code evaluates a sparse polynomial reading only the variables it carries. -/
@[csimp] theorem CMvPolynomial.eval_eq_evalFast :
    @CMvPolynomial.eval = @CMvPolynomial.evalFast := by
  funext R _ n vs p
  simp only [CMvPolynomial.eval, CMvPolynomial.eval₂, CMvPolynomial.evalFast, evalMonomialFast_eq,
    RingHom.id_apply]

end
end LeanerVM.Protocol
