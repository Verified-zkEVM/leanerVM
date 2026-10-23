/-
  LeanerVM.Protocol.ToCompPoly.FinLoop

  Sums, products and Horner's rule over `Fin n` as loops, for compiled code. Candidate for
  CompPoly.
-/

module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Sums and products as loops

A `Finset.sum` over `Fin n` compiles to a fold over the list of the indices, built for each sum.
`sumFin f` and `prodFin f` are `Σ_i f i` and `∏_i f i` as `Fin.foldl` loops, with no list
(`sumFin_eq_sum`, `prodFin_eq_prod`), and `hornerFin f x` is `Σ_i x ^ i · f i` by Horner's rule,
one product per term (`hornerFin_eq_sum`). Nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

@[expose] public section

/-- `Σ_i f i` as a loop over the indices. -/
def sumFin {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) : M :=
  Fin.foldl n (fun acc i ↦ acc + f i) 0

/-- The loop is the sum. -/
theorem sumFin_eq_sum {M : Type*} [AddCommMonoid M] : {n : ℕ} → (f : Fin n → M) →
    sumFin f = ∑ i, f i
  | 0, f => by simp [sumFin]
  | n + 1, f => by
    rw [sumFin, Fin.foldl_succ_last, Fin.sum_univ_castSucc, ← sumFin_eq_sum, sumFin]

/-- `∏_i f i` as a loop over the indices. -/
def prodFin {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) : M :=
  Fin.foldl n (fun acc i ↦ acc * f i) 1

/-- The loop is the product. -/
theorem prodFin_eq_prod {M : Type*} [CommMonoid M] : {n : ℕ} → (f : Fin n → M) →
    prodFin f = ∏ i, f i
  | 0, f => by simp [prodFin]
  | n + 1, f => by
    rw [prodFin, Fin.foldl_succ_last, Fin.prod_univ_castSucc, ← prodFin_eq_prod, prodFin]

/-- `Σ_i x ^ i · f i` by Horner's rule: `f 0 + x · (f 1 + x · (…))`. -/
def hornerFin {R : Type*} [CommRing R] {n : ℕ} (f : Fin n → R) (x : R) : R :=
  Fin.foldr n (fun i acc ↦ f i + x * acc) 0

/-- Horner's rule is the sum of the powers. -/
theorem hornerFin_eq_sum {R : Type*} [CommRing R] : {n : ℕ} → (f : Fin n → R) → (x : R) →
    hornerFin f x = ∑ i : Fin n, x ^ i.val * f i
  | 0, f, x => by simp [hornerFin]
  | n + 1, f, x => by
    rw [hornerFin, Fin.foldr_succ, ← hornerFin, hornerFin_eq_sum, Fin.sum_univ_succ,
      Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ, mul_assoc, mul_left_comm]

end
end LeanerVM.Protocol
