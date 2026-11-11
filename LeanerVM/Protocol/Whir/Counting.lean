/-
  LeanerVM.Protocol.Whir.Counting

  The counting arguments of the soundness of WHIR's opening: a batching challenge over a list of
  candidates, one more coordinate of the out-of-domain point, and the query positions. Candidate
  for ArkLib.
-/

module

public import LeanerVM.Protocol.Whir.Word
public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToCompPoly.Restriction
public import LeanerVM.Protocol.ToCompPoly.PowerBatching

/-!
# Counting bad challenges

Category B: Annex B, proof of `thm:rbr`. Each bound counts the challenges that let a prover
escape, in the form `sampleChallengeSecurity` takes; the error is the count over the size of the
challenge space.

* `card_batch_exists_zero_le` (the batching challenge): for a finite list of candidates, each
  violating at least one of `J` claims, at most `(J - 1)` challenges per candidate make the
  batched discrepancy of some candidate vanish, a polynomial of degree below `J` that is not
  zero (`card_false_batch_le`): at most `(J - 1) · |list|` in all;
* `card_ood_bad_le` (the out-of-domain point, one coordinate at a time): for a finite list of
  tables none of whose pairs has a difference that vanishes on the coordinates drawn so far,
  at most `C(|list|, 2)` values of the next coordinate make some pair's difference vanish: a table
  that is not zero on a partial point is zero on one more coordinate at one value at most
  (`natCard_restrictedZero_update_le`), one value per unordered pair. Summed over the `ν`
  coordinates this is the pinned `C(L, 2) · ν / |E|`, the error spread over the draws;
* `card_positions_le` (the query positions): `t` independent positions all fall in a set of at
  most `a` of the `N` positions in at most `a ^ t` of the `N ^ t` choices, so with probability at
  most `(a / N) ^ t`; a set of agreements below the threshold has at most `a - 1`, and
  `((a - 1) / N) ^ t < (1 - γ) ^ t`.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval
open scoped NNReal

@[expose] public section

namespace Whir

/-- Batching by powers over a finite list of candidates: if each candidate's discrepancy vector is
nonzero, at most `(J - 1)` challenges per candidate make some candidate's batched discrepancy
vanish. -/
theorem card_batch_exists_zero_le {X : Type} [Finite X] {J : ℕ} (d : X → Fin J → E)
    (hd : ∀ x, ∃ j, d x j ≠ 0) :
    Nat.card {ρ : E // ∃ x, powerBatch (d x) ρ = 0} ≤ (J - 1) * Nat.card X := by
  classical
  have := Fintype.ofFinite E
  have := Fintype.ofFinite X
  rw [natCard_subtype_eq_card_filter, Nat.card_eq_fintype_card (α := X)]
  calc _ ≤ (Finset.univ.biUnion fun x : X ↦
          Finset.univ.filter fun ρ : E ↦ powerBatch (d x) ρ = 0).card := by
        refine Finset.card_le_card fun ρ hρ ↦ ?_
        obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hρ).2
        exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
    _ ≤ ∑ x : X, (Finset.univ.filter fun ρ : E ↦ powerBatch (d x) ρ = 0).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _x : X, (J - 1) := Finset.sum_le_sum fun x _ ↦ by
        obtain ⟨j, hj⟩ := hd x
        have h := card_false_batch_le (d x) (0 : Fin J → E) ⟨j, by simpa using hj⟩
        exact le_trans (le_of_eq (congrArg Finset.card
          (Finset.filter_congr fun ρ _ ↦ by simp [powerBatch]))) h
    _ = Fintype.card X * (J - 1) := by simp
    _ = (J - 1) * Fintype.card X := mul_comm _ _

/-- The out-of-domain point, one coordinate at a time: for a finite list of tables none of whose
pairs is zero on the partial point, at most `C(L, 2)` values of one more coordinate make some
pair's difference zero on the point with it fixed. -/
theorem card_ood_bad_le {ν : ℕ} (𝓛 : Finset (CMlPolynomialEval E ν)) (σ : Partial E) (k : ℕ)
    (hσ : ∀ g ∈ 𝓛, ∀ g' ∈ 𝓛, g ≠ g' → ¬ RestrictedZero (diffTable g g') σ) :
    Nat.card {x : E // ∃ g ∈ 𝓛, ∃ g' ∈ 𝓛, g ≠ g' ∧
      RestrictedZero (diffTable g g') (Function.update σ k (some x))} ≤ 𝓛.card.choose 2 := by
  classical
  have := Fintype.ofFinite E
  rw [natCard_subtype_eq_card_filter]
  calc _ ≤ ((𝓛.powersetCard 2).biUnion fun s ↦ Finset.univ.filter fun x : E ↦
          ∃ g ∈ s, ∃ g' ∈ s, g ≠ g' ∧
            RestrictedZero (diffTable g g') (Function.update σ k (some x))).card := by
        refine Finset.card_le_card fun x hx ↦ ?_
        obtain ⟨g, hg, g', hg', hne, hz⟩ := (Finset.mem_filter.mp hx).2
        refine Finset.mem_biUnion.mpr ⟨{g, g'}, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        · rw [Finset.mem_powersetCard]
          refine ⟨?_, Finset.card_pair hne⟩
          intro z hz'
          rcases Finset.mem_insert.mp hz' with rfl | hz'
          · exact hg
          · rw [Finset.mem_singleton.mp hz']
            exact hg'
        · exact ⟨g, by simp, g', by simp, hne, hz⟩
    _ ≤ ∑ s ∈ 𝓛.powersetCard 2, (Finset.univ.filter fun x : E ↦
          ∃ g ∈ s, ∃ g' ∈ s, g ≠ g' ∧
            RestrictedZero (diffTable g g') (Function.update σ k (some x))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ 𝓛.powersetCard 2, 1 := by
        refine Finset.sum_le_sum fun s hs ↦ ?_
        obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hs
        obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
        have ha : a ∈ 𝓛 := hsub (by simp)
        have hb : b ∈ 𝓛 := hsub (by simp)
        have hnz := hσ a ha b hb hab
        have h1 := natCard_restrictedZero_update_le (diffTable a b) σ k hnz
        rw [natCard_subtype_eq_card_filter] at h1
        refine le_trans (Finset.card_le_card fun x hx ↦ ?_) h1
        obtain ⟨g, hg, g', hg', hne, hz⟩ := (Finset.mem_filter.mp hx).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hsym : ∀ x : E, RestrictedZero (diffTable b a) (Function.update σ k (some x)) →
            RestrictedZero (diffTable a b) (Function.update σ k (some x)) := by
          intro x h p
          have := h p
          rw [evalMle_diffTable] at this ⊢
          linear_combination -this
        simp only [Finset.mem_insert, Finset.mem_singleton] at hg hg'
        rcases hg with rfl | rfl <;> rcases hg' with rfl | rfl
        · exact absurd rfl hne
        · exact hz
        · exact hsym x hz
        · exact absurd rfl hne
    _ = 𝓛.card.choose 2 := by simp [Finset.card_powersetCard]

/-- A set of at most `a` positions out of `N` holds `t` independent positions in at most
`a ^ t` of the `N ^ t` choices. -/
theorem card_positions_le {N t a : ℕ} (S : Finset (Fin N)) (hS : S.card ≤ a) :
    Nat.card {pos : Fin t → Fin N // ∀ q, pos q ∈ S} ≤ a ^ t := by
  classical
  have e : {pos : Fin t → Fin N // ∀ q, pos q ∈ S} ≃ (Fin t → S) :=
    Equiv.subtypePiEquivPi
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
  exact Nat.pow_le_pow_left hS t

/-- `a ^ t` choices of `t` positions out of `N ^ t` have probability `(a / N) ^ t`. The query
positions' error counts `a - 1` agreements for the threshold `a = ⌈(1 - γ) N⌉`, below
`(1 - γ) ^ t`. -/
theorem positions_err_eq (a N t : ℕ) :
    ((a ^ t : ℕ) : ℝ≥0) / (Nat.card (Fin t → Fin N) : ℝ≥0) = ((a : ℝ≥0) / (N : ℝ≥0)) ^ t := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  push_cast
  rw [div_pow]

end Whir

end

end LeanerVM.Protocol
