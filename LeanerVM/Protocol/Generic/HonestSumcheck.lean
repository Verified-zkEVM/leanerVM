/-
Copyright (c) 2026 leanerVM Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic)

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
-/
/-
  LeanerVM.Protocol.Generic.HonestSumcheck

  Honest sumcheck polynomials and their algebraic identities.
-/

module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev

/-!
# Honest sumcheck algebra

Category A: the honest-round identities in `fact:sumcheck`,
`doc/leanvm/body/03-proving-primitives.tex`, and the high-first convention in §5's
`doc/leanvm/body/05-arithmetization.tex` (`sec:air`), at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`.

The suffix-sum algebra is derived from Verified-zkEVM/leanth at
`23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`,
`Leanth/ProofSystem/ZeroCheck.lean:3455-3675`; its original notice is retained above.
This port exposes that algebra independently of the old verifier and certificates.
The immediate consumer is the honest strategy in the protocol blueprint's sumcheck layer,
tracked by [ArkLib #1](https://github.com/Verified-zkEVM/ArkLib/issues/1). This pinned compatibility
module preserves the original semiring scope. The separate upstream adapter identifies its
polynomial with ArkLib's existing projected round when the Boolean embedding is available;
retire compatibility definitions after explicit adoption of an equivalent upstream API.

Pinned staging is tracked by [leanerVM #37](https://github.com/Verified-zkEVM/leanerVM/issues/37).

Coordinate `k` is bound in round `k`. Coordinates refer to the polynomial's variable names;
for the VM's high-first convention, pass `sumcheckHighFirst P`, which renames by `Fin.rev`.
The terminal identity concerns the corresponding ordered challenge function. No polynomial
here is selected by assuming that an honest message with the desired properties exists.
This module proves completeness identities and an individual-degree bound. Its declarations
make no claim about the deployed transcript encoding or the full virtual-table sumcheck.
-/

namespace LeanerVM.Protocol

@[expose] public section

/-- Boolean assignments with the first `k` coordinates fixed to zero; only the suffix is free. -/
def sumcheckFreeCube (m k : Nat) : Finset (Fin m → Fin 2) :=
  Finset.univ.filter (fun b ↦ ∀ i : Fin m, (i : Nat) < k → b i = 0)

/-- Substitute the sampled prefix and current challenge into a suffix assignment. -/
def sumcheckMixPoint {F : Type*} [CommSemiring F] {m : Nat}
    (k : Nat) (c : Fin k → F) (y : F) (b : Fin m → Fin 2) : Fin m → F :=
  fun i ↦ if h : (i : Nat) < k then c ⟨i, h⟩
    else if (i : Nat) = k then y else (((b i : Fin 2) : Nat) : F)

/-- The honest round polynomial, obtained by summing over the unbound Boolean suffix. -/
noncomputable def sumcheckRoundPoly {F : Type*} [CommSemiring F] {m : Nat}
    (P : MvPolynomial (Fin m) F) (k : Nat) (c : Fin k → F) : Polynomial F :=
  (sumcheckFreeCube m (k + 1)).sum fun b ↦
    MvPolynomial.eval₂ Polynomial.C
      (fun i : Fin m ↦ if h : (i : Nat) < k then Polynomial.C (c ⟨i, h⟩)
        else if (i : Nat) = k then Polynomial.X
        else Polynomial.C ((((b i : Fin 2) : Nat) : F))) P

/-- Evaluating the honest round polynomial performs the corresponding substitutions. -/
theorem sumcheck_eval_roundPoly {F : Type*} [CommSemiring F] {m : Nat}
    (P : MvPolynomial (Fin m) F) (k : Nat) (c : Fin k → F) (y : F) :
    Polynomial.eval y (sumcheckRoundPoly P k c) =
      (sumcheckFreeCube m (k + 1)).sum fun b ↦
        MvPolynomial.eval (sumcheckMixPoint k c y b) P := by
  rw [sumcheckRoundPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  change (Polynomial.evalRingHom y) (MvPolynomial.eval₂ _ _ P) = _
  rw [MvPolynomial.eval₂_comp_left, Polynomial.evalRingHom,
    Polynomial.eval₂RingHom_comp_C, MvPolynomial.eval]
  congr 1
  funext i
  by_cases h : (i : Nat) < k
  · simp [sumcheckMixPoint, h]
  · by_cases h2 : (i : Nat) = k <;> simp [sumcheckMixPoint, h, h2]

/-- Zeroing the next coordinate moves to the next free cube. -/
theorem mem_sumcheckFreeCube_update_zero {m : Nat} (k : Nat) (hk : k < m)
    (b : Fin m → Fin 2) (hb : b ∈ sumcheckFreeCube m k) :
    Function.update b ⟨k, hk⟩ 0 ∈ sumcheckFreeCube m (k + 1) := by
  -- Zeroing coordinate `k` of a point of `sumcheckFreeCube m k` lands in
  -- `sumcheckFreeCube m (k+1)`.  One of the two membership obligations of the
  -- `Finset.sum_nbij'` below.  It takes nothing from that proof but the arithmetic
  -- side-condition `hk`, and in particular not the summand `f`.
  classical
  simp only [sumcheckFreeCube, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  intro i hi
  by_cases hik : i = ⟨k, hk⟩
  · rw [hik, Function.update_self]
  · rw [Function.update_of_ne hik]
    refine hb i ?_
    have : (i : Nat) ≠ k := fun hc ↦ hik (Fin.ext hc)
    omega

/-- Restoring a Boolean value moves back to the preceding free cube. -/
theorem mem_sumcheckFreeCube_update {m : Nat} (k : Nat) (hk : k < m) (t : Fin 2)
    (b : Fin m → Fin 2) (hb : b ∈ sumcheckFreeCube m (k + 1)) :
    Function.update b ⟨k, hk⟩ t ∈ sumcheckFreeCube m k := by
  -- Writing any value into coordinate `k` of a point of `sumcheckFreeCube m (k+1)` lands back in
  -- `sumcheckFreeCube m k`.  The other membership obligation; same hypothesis profile.
  classical
  simp only [sumcheckFreeCube, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  intro i hi
  have hik : i ≠ ⟨k, hk⟩ := fun hc ↦ by rw [hc] at hi; simp at hi
  rw [Function.update_of_ne hik]
  exact hb i (by omega)

/-- Split a free cube into the two values of its next coordinate. -/
theorem sumcheck_sum_freeCube_split {F : Type*} [AddCommMonoid F] {m : Nat}
    (k : Nat) (hk : k < m) (f : (Fin m → Fin 2) → F) :
    (sumcheckFreeCube m k).sum f =
      Finset.univ.sum fun t : Fin 2 ↦
        (sumcheckFreeCube m (k + 1)).sum fun b ↦ f (Function.update b ⟨k, hk⟩ t) := by
  classical
  set K : Fin m := ⟨k, hk⟩ with hK
  rw [show (Finset.univ.sum fun t : Fin 2 ↦
        (sumcheckFreeCube m (k + 1)).sum fun b ↦ f (Function.update b K t))
      = ((Finset.univ : Finset (Fin 2)) ×ˢ sumcheckFreeCube m (k + 1)).sum
          (fun p ↦ f (Function.update p.2 K p.1)) from
    (Finset.sum_product _ _
      (fun p : Fin 2 × (Fin m → Fin 2) ↦ f (Function.update p.2 K p.1))).symm]
  refine Finset.sum_nbij' (i := fun b ↦ (b K, Function.update b K 0))
    (j := fun p ↦ Function.update p.2 K p.1) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simpa only [Finset.mem_product, Finset.mem_univ, true_and] using
      mem_sumcheckFreeCube_update_zero k hk b hb
  · intro p hp
    exact mem_sumcheckFreeCube_update k hk p.1 p.2 (Finset.mem_product.mp hp).2
  · intro b _
    simp only
    rw [Function.update_idem, Function.update_eq_self]
  · intro p hp
    simp only [Finset.mem_product, sumcheckFreeCube, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    have h2 : p.2 K = 0 := hp K (by simp [hK])
    simp only [Function.update_self, Function.update_idem]
    rw [← h2, Function.update_eq_self]
  · intro b _
    simp only
    rw [Function.update_idem, Function.update_eq_self]

/-- After all coordinates are bound, the free cube has one representative. -/
theorem sumcheck_freeCube_full (m : Nat) :
    sumcheckFreeCube m m = {fun _ ↦ 0} := by
  ext b
  simp only [sumcheckFreeCube, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro h
    funext i
    exact h i i.isLt
  · intro h i _
    rw [h]

/-- Before any coordinate is bound, the entire Boolean cube is free. -/
theorem sumcheck_freeCube_zero (m : Nat) :
    sumcheckFreeCube m 0 = Finset.univ := by
  ext b
  simp [sumcheckFreeCube]

/-- The last round evaluated at its challenge equals the original polynomial evaluation. -/
theorem sumcheck_roundPoly_terminal {F : Type*} [CommSemiring F] {m : Nat}
    (P : MvPolynomial (Fin m) F) (z : Fin m → F) (hm : 0 < m) :
    Polynomial.eval (z ⟨m - 1, by omega⟩)
        (sumcheckRoundPoly P (m - 1)
          (fun i : Fin (m - 1) ↦ z ⟨i, by have := i.isLt; omega⟩))
      = MvPolynomial.eval z P := by
  rw [sumcheck_eval_roundPoly, show m - 1 + 1 = m from by omega, sumcheck_freeCube_full,
    Finset.sum_singleton]
  refine congrArg (fun w : Fin m → F ↦ MvPolynomial.eval w P) (funext fun i ↦ ?_)
  simp only [sumcheckMixPoint]
  split_ifs with h1 h2
  · rfl
  · exact congrArg z (Fin.ext h2.symm)
  · have := i.isLt; omega

/-- Adjacent honest round polynomials satisfy the sumcheck chaining equation. -/
theorem sumcheck_roundPoly_chain {F : Type*} [CommSemiring F] {m : Nat}
    (P : MvPolynomial (Fin m) F) (z : Fin m → F) (k : Nat) (hk : k + 1 < m) :
    Polynomial.eval 0 (sumcheckRoundPoly P (k + 1)
          (fun i : Fin (k + 1) ↦ z ⟨i, by have := i.isLt; omega⟩)) +
        Polynomial.eval 1 (sumcheckRoundPoly P (k + 1)
          (fun i : Fin (k + 1) ↦ z ⟨i, by have := i.isLt; omega⟩))
      = Polynomial.eval (z ⟨k, by omega⟩)
          (sumcheckRoundPoly P k (fun i : Fin k ↦ z ⟨i, by have := i.isLt; omega⟩)) := by
  rw [sumcheck_eval_roundPoly, sumcheck_eval_roundPoly, sumcheck_eval_roundPoly,
    sumcheck_sum_freeCube_split (k + 1) hk
      (fun b ↦ MvPolynomial.eval
        (sumcheckMixPoint k (fun i : Fin k ↦ z ⟨i, by have := i.isLt; omega⟩)
          (z ⟨k, by omega⟩) b) P),
    Fin.sum_univ_two]
  congr 1 <;>
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    refine congrArg (fun w : Fin m → F ↦ MvPolynomial.eval w P) (funext fun i ↦ ?_)
    by_cases h1 : (i : Nat) < k
    · simp [sumcheckMixPoint, h1, Nat.lt_succ_of_lt h1]
    · by_cases h2 : (i : Nat) = k
      · simp [sumcheckMixPoint, h2]
      · by_cases h3 : (i : Nat) = k + 1
        · have hik : i = (⟨k + 1, hk⟩ : Fin m) := Fin.ext h3
          rw [hik]
          simp [sumcheckMixPoint, Function.update_self]
        · simp [sumcheckMixPoint, h1, h2, h3,
            show ¬ (i : Nat) < k + 1 from by omega,
            show i ≠ (⟨k + 1, hk⟩ : Fin m) from fun hc ↦ h3 (by simp [hc])]

/-- The first endpoint sum equals the original Boolean cube sum. -/
theorem sumcheck_roundPoly_initial {F : Type*} [CommSemiring F] {m : Nat}
    (P : MvPolynomial (Fin m) F) (c : Fin 0 → F) (hm : 0 < m) :
    Polynomial.eval 0 (sumcheckRoundPoly P 0 c) +
        Polynomial.eval 1 (sumcheckRoundPoly P 0 c)
      = Finset.univ.sum fun b : Fin m → Fin 2 ↦
          MvPolynomial.eval (fun i ↦ (((b i : Fin 2) : Nat) : F)) P := by
  rw [sumcheck_eval_roundPoly, sumcheck_eval_roundPoly, ← sumcheck_freeCube_zero m,
    sumcheck_sum_freeCube_split 0 hm
      (fun b ↦ MvPolynomial.eval (fun i ↦ (((b i : Fin 2) : Nat) : F)) P),
    Fin.sum_univ_two]
  congr 1 <;>
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    refine congrArg (fun w : Fin m → F ↦ MvPolynomial.eval w P) (funext fun i ↦ ?_)
    by_cases h2 : (i : Nat) = 0
    · have hik : i = (⟨0, hm⟩ : Fin m) := Fin.ext h2
      rw [hik, Function.update_self]
      simp [sumcheckMixPoint]
    · rw [Function.update_of_ne
        (show i ≠ (⟨0, hm⟩ : Fin m) from fun hc ↦ h2 (by simp [hc]))]
      simp [sumcheckMixPoint, h2]

/-- The honest round degree is bounded by the individual degree of its bound variable. -/
theorem sumcheck_natDegree_roundPoly_le {F : Type*} [CommSemiring F] {m : Nat}
    (P : MvPolynomial (Fin m) F) (k : Fin m) (c : Fin (k : Nat) → F) :
    (sumcheckRoundPoly P (k : Nat) c).natDegree ≤ MvPolynomial.degreeOf k P := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b _ ↦ ?_
  rw [MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd ↦ ?_
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun i : Fin m ↦ if i = k then d i else 0)
    fun i _ ↦ ?_) ?_
  · by_cases hik : i = k
    · subst hik
      refine le_trans (Polynomial.natDegree_pow_le) ?_
      simpa using Nat.mul_le_mul_left (d i) (Polynomial.natDegree_X_le (R := F))
    · refine le_trans (Polynomial.natDegree_pow_le) ?_
      simp only [hik, if_false, Nat.le_zero, Nat.mul_eq_zero]
      right
      by_cases h : (i : Nat) < (k : Nat)
      · simp [h]
      · have hne : (i : Nat) ≠ (k : Nat) := fun hc ↦ hik (Fin.ext hc)
        simp [h, hne]
  · rw [Finset.sum_ite_eq' d.support k]
    by_cases hk : k ∈ d.support
    · rw [if_pos hk, MvPolynomial.degreeOf_eq_sup]
      exact Finset.le_sup (f := fun e : Fin m →₀ Nat ↦ e k) hd
    · simp [hk]
/-- With zero variables, the cube sum is the unique terminal evaluation: there are no rounds. -/
theorem sumcheck_zero_rounds {F : Type*} [CommSemiring F]
    (P : MvPolynomial (Fin 0) F) :
    (∑ b : Fin 0 → Fin 2, MvPolynomial.eval (fun i ↦ ((b i).val : F)) P) =
      MvPolynomial.eval Fin.elim0 P := by
  simp only [Finset.univ_unique, Finset.sum_singleton]
  congr 2
  funext i
  exact Fin.elim0 i

/-- Rename variables so that increasing round numbers bind original variables high first. -/
noncomputable def sumcheckHighFirst {F : Type*} [CommSemiring F] {m : ℕ}
    (P : MvPolynomial (Fin m) F) : MvPolynomial (Fin m) F :=
  MvPolynomial.rename Fin.rev P

/-- High-first round `k` uses the individual degree of original coordinate `k.rev`. -/
theorem sumcheck_highFirst_natDegree_le {F : Type*} [CommSemiring F] {m : ℕ}
    (P : MvPolynomial (Fin m) F) (k : Fin m) (c : Fin k.val → F) :
    (sumcheckRoundPoly (sumcheckHighFirst P) k.val c).natDegree ≤
      MvPolynomial.degreeOf k.rev P := by
  calc
    _ ≤ MvPolynomial.degreeOf k (sumcheckHighFirst P) :=
      sumcheck_natDegree_roundPoly_le _ k c
    _ = MvPolynomial.degreeOf k.rev P := by
      simpa [sumcheckHighFirst] using
        (MvPolynomial.degreeOf_rename_of_injective (p := P) Fin.rev_injective k.rev)

/-- Every high-first round evaluates the original polynomial at the reversed mixed point. -/
theorem sumcheck_highFirst_round {F : Type*} [CommSemiring F] {m : ℕ}
    (P : MvPolynomial (Fin m) F) (k : ℕ) (c : Fin k → F) (y : F) :
    Polynomial.eval y (sumcheckRoundPoly (sumcheckHighFirst P) k c) =
      ∑ b ∈ sumcheckFreeCube m (k + 1),
        MvPolynomial.eval (fun i ↦ sumcheckMixPoint k c y b i.rev) P := by
  rw [sumcheck_eval_roundPoly]
  apply Finset.sum_congr rfl
  intro b _
  rw [sumcheckHighFirst, MvPolynomial.eval_rename]
  rfl

/-- The high-first terminal equation explicitly reverses the ordered challenge coordinates. -/
theorem sumcheck_highFirst_terminal {F : Type*} [CommSemiring F] {m : ℕ}
    (P : MvPolynomial (Fin m) F) (z : Fin m → F) (hm : 0 < m) :
    Polynomial.eval (z ⟨m - 1, by omega⟩)
      (sumcheckRoundPoly (sumcheckHighFirst P) (m - 1)
        (fun i : Fin (m - 1) ↦ z ⟨i, by have := i.isLt; omega⟩)) =
      MvPolynomial.eval (fun i ↦ z i.rev) P := by
  rw [sumcheck_roundPoly_terminal _ z hm, sumcheckHighFirst, MvPolynomial.eval_rename]
  rfl

end
end LeanerVM.Protocol
