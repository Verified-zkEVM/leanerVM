/-
Copyright (c) 2026 leanerVM Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas, Elias Judin

Derived-source notice:
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
-/
/-
  LeanerVM.Protocol.Generic.HonestSumcheckUpstream

  Polynomial correspondence with the pinned ArkLib honest-round API.
-/

module

public import LeanerVM.Protocol.Generic.HonestSumcheck
public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Pinned honest-round correspondence

The zero-padded Boolean suffix representation agrees as a polynomial with ArkLib's existing
`projectedRoundPolynomial`. The adapter explicitly requires the Boolean embedding; the original
honest algebra retains its `CommSemiring` scope, including trivial semirings. The sharper degree
bound belongs to the existing upstream polynomial and does not introduce another round definition.

The selected-variable coefficient-map proof adapts
`toPoly_eval₂_CHom_insertNth` in ArkLib's `Commitments/Functional/Hachi/Sumcheck/RoundPoly.lean`
at `dca90385fb40dd5eb8da9145da6348ed17f5cd8b`; its source notice is retained above.

This is compatibility staging for the sumcheck consumer at the recorded dependency pin. Upstream
ownership is [ArkLib #1](https://github.com/Verified-zkEVM/ArkLib/issues/1); remove the adapter after
an explicit pin adoption supplies the same transports. It makes no multi-round security claim.
-/

namespace LeanerVM.Protocol

@[expose] public section

open Finset Polynomial MvPolynomial
open Sumcheck.Spec.SingleRound

/-- Pad a Boolean suffix with zero through the current coordinate. -/
def sumcheckPadSuffix {n : ℕ} (k : Fin (n + 1)) (b : Fin (n - k.val) → Fin 2) :
    Fin (n + 1) → Fin 2 :=
  fun j ↦ if h : k.val < j.val then b ⟨j.val - k.val - 1, by omega⟩ else 0

/-- Zero-padded assignments enumerate each Boolean suffix exactly once. -/
theorem sumcheck_sum_freeCube_suffix {A : Type*} [AddCommMonoid A] {n : ℕ}
    (k : Fin (n + 1)) (f : (Fin (n + 1) → Fin 2) → A) :
    ∑ b ∈ sumcheckFreeCube (n + 1) (k.val + 1), f b =
      ∑ b : Fin (n - k.val) → Fin 2, f (sumcheckPadSuffix k b) := by
  classical
  refine Finset.sum_nbij' (fun b j ↦ b ⟨k.val + 1 + j.val, by omega⟩)
    (sumcheckPadSuffix k) ?_ ?_ ?_ ?_ ?_
  · intro b _
    exact Finset.mem_univ _
  · intro b _
    simp only [sumcheckFreeCube, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj
    simp [sumcheckPadSuffix, show ¬k.val < j.val by omega]
  · intro b hb
    funext j
    simp only [sumcheckPadSuffix]
    split_ifs with h
    · congr 1
      apply Fin.ext
      simp
      omega
    · exact (Finset.mem_filter.mp hb).2 j (by omega) |>.symm
  · intro b _
    funext j
    simp only [sumcheckPadSuffix, show k.val < k.val + 1 + j.val by omega, ↓reduceDIte]
    congr 1
    apply Fin.ext
    simp
    omega
  · intro b hb
    symm
    congr 1
    funext j
    simp only [sumcheckPadSuffix]
    split_ifs with h
    · congr 1
      apply Fin.ext
      simp
      omega
    · exact (Finset.mem_filter.mp hb).2 j (by omega) |>.symm

/-- Boolean values embedded as zero and one, only at the nontrivial upstream boundary. -/
def sumcheckBooleanEmbedding (R : Type) [CommSemiring R] [Nontrivial R] : Fin 2 ↪ R where
  toFun b := (b.val : R)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

/-- Summing over an embedded Boolean cube is summing over its Boolean coordinates. -/
theorem sumcheck_sum_embedded_cube {R A : Type*} [AddCommMonoid A] (D : Fin 2 ↪ R)
    (m : ℕ) (f : (Fin m → R) → A) :
    ∑ x ∈ (univ.map D) ^ᶠ m, f x = ∑ b : Fin m → Fin 2, f (fun j ↦ D (b j)) := by
  classical
  have hset : (univ.map D) ^ᶠ m =
      (univ : Finset (Fin m → Fin 2)).image (fun b j ↦ D (b j)) := by
    ext x
    simp only [Fintype.mem_piFinset, Finset.mem_map, Finset.mem_univ, true_and,
      Finset.mem_image]
    exact ⟨fun h ↦ ⟨fun j ↦ (h j).choose, funext fun j ↦ (h j).choose_spec⟩,
      fun ⟨b, hb⟩ j ↦ ⟨b j, congrFun hb j⟩⟩
  rw [hset, Finset.sum_image]
  intro a _ b _ h
  funext j
  exact D.injective (congrFun h j)

/-- Mapping the coefficients of the selected-variable representation is direct substitution. -/
theorem sumcheck_map_finSuccEquivNth {R : Type*} [CommSemiring R] {n : ℕ}
    (k : Fin (n + 1)) (s : Fin n → R) (p : MvPolynomial (Fin (n + 1)) R) :
    Polynomial.map (MvPolynomial.eval s) (finSuccEquivNth R k p) =
      MvPolynomial.eval₂ Polynomial.C
        (Fin.insertNth k Polynomial.X (fun j ↦ Polynomial.C (s j))) p := by
  rw [MvPolynomial.finSuccEquivNth_apply, MvPolynomial.coe_eval₂Hom]
  change (Polynomial.mapRingHom (MvPolynomial.eval s))
    (MvPolynomial.eval₂ _ _ p) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp
  · funext j
    refine Fin.succAboveCases k ?_ ?_ j
    · simp [Fin.insertNth_apply_same]
    · intro l
      simp [Fin.insertNth_apply_succAbove]

/-- The padded Boolean assignment is the upstream prefix/suffix insertion, coefficientwise. -/
theorem sumcheck_substitution_eq {R : Type} [CommSemiring R] {n : ℕ}
    (k : Fin (n + 1)) (c : Fin k.val → R) (b : Fin (n - k.val) → Fin 2) :
    (fun j : Fin (n + 1) ↦ if h : j.val < k.val then Polynomial.C (c ⟨j, h⟩)
      else if j.val = k.val then Polynomial.X
      else Polynomial.C ((sumcheckPadSuffix k b j).val : R)) =
      Fin.insertNth k Polynomial.X
        (fun j ↦ Polynomial.C (roundSuffix R n k c (fun l ↦ ((b l).val : R)) j)) := by
  funext j
  rcases lt_trichotomy j k with h | h | h
  · rw [Fin.insertNth_apply_below h]
    simp [roundSuffix, Fin.append, Fin.addCases, show j.val < k.val from h]
    congr 1
  · subst j
    simp
  · rw [Fin.insertNth_apply_above h]
    simp only [roundSuffix, Fin.val_castSucc, Fin.append, Function.comp_apply,
      Fin.addCases, Fin.val_cast, Fin.val_pred,
      show ¬j.val - 1 < k.val by omega, ↓reduceDIte, Fin.cast_cast,
      eq_rec_constant, show ¬j.val < k.val by omega,
      show j.val ≠ k.val by omega, ↓reduceIte, sumcheckPadSuffix,
      show k.val < j.val from h]
    congr 4
    apply Fin.ext
    simp
    omega

/-- Exact polynomial equality with the existing pinned ArkLib honest round. -/
theorem sumcheckRoundPoly_eq_projectedRoundPolynomial {R : Type} [CommSemiring R]
    [Nontrivial R] {n deg : ℕ} (k : Fin (n + 1)) (c : Fin k.val → R)
    (p : Sumcheck.Spec.OracleStatement R (n + 1) deg ()) :
    sumcheckRoundPoly p.val k.val c =
      (projectedRoundPolynomial R (n + 1) deg (sumcheckBooleanEmbedding R) k c p).val := by
  classical
  rw [sumcheckRoundPoly, sumcheck_sum_freeCube_suffix k]
  change _ = ∑ x ∈ (univ.map (sumcheckBooleanEmbedding R)) ^ᶠ (n - k.val),
    Polynomial.map (MvPolynomial.eval (roundSuffix R n k c x))
      (MvPolynomial.finSuccEquivNth R k p.val)
  rw [sumcheck_sum_embedded_cube]
  apply Finset.sum_congr rfl
  intro b _
  rw [sumcheck_map_finSuccEquivNth, sumcheck_substitution_eq]
  rfl

/-- The round adapter binds original coordinates high first by renaming with `Fin.rev`. -/
theorem sumcheckHighFirst_eval {R : Type*} [CommSemiring R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (z : Fin n → R) :
    MvPolynomial.eval z (sumcheckHighFirst p) =
      MvPolynomial.eval (fun i ↦ z i.rev) p := by
  rw [sumcheckHighFirst, MvPolynomial.eval_rename]
  rfl

/-- A trivial coefficient semiring cannot support the upstream Boolean embedding. -/
theorem sumcheck_no_boolean_embedding (R : Type*) [Subsingleton R] : IsEmpty (Fin 2 ↪ R) := by
  refine ⟨fun e ↦ ?_⟩
  have h : (0 : Fin 2) = 1 := e.injective (Subsingleton.elim _ _)
  exact Fin.zero_ne_one h

/-- The pinned upstream polynomial has the sharper degree bound at the bound coordinate. -/
theorem projectedRoundPolynomial_natDegree_le {R : Type} [CommSemiring R]
    {n deg m : ℕ} (D : Fin m ↪ R) (k : Fin (n + 1))
    (c : Fin k.castSucc → R) (p : Sumcheck.Spec.OracleStatement R (n + 1) deg ()) :
    (projectedRoundPolynomial R (n + 1) deg D k c p).val.natDegree ≤ degreeOf k p.val := by
  change (∑ x ∈ (univ.map D) ^ᶠ (n - k),
    Polynomial.map (MvPolynomial.eval (roundSuffix R n k c x))
      (MvPolynomial.finSuccEquivNth R k p.val)).natDegree ≤ _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  exact Polynomial.natDegree_map_le.trans (le_of_eq (natDegree_finSuccEquivNth _))

end
end LeanerVM.Protocol
