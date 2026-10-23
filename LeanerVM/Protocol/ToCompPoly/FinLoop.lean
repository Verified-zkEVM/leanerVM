/-
  LeanerVM.Protocol.ToCompPoly.FinLoop

  Sums and products over `Fin n` as loops, for compiled code. Candidate for CompPoly.
-/

module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Sums and products as loops

A `Finset.sum` over `Fin n` compiles to a fold over the list of the indices, built for each sum.
`sumFin f` and `prodFin f` are `Σ_i f i` and `∏_i f i` as `Fin.foldl` loops, with no list
(`sumFin_eq_sum`, `prodFin_eq_prod`). Nothing here transcribes a source.
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

end
end LeanerVM.Protocol
