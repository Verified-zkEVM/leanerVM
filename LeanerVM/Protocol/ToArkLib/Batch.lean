/-
  LeanerVM.Protocol.ToArkLib.Batch

  Batching by powers as a component: the verifier draws one challenge and combines the claimed
  values by its powers. Completeness and round-by-round knowledge soundness at `(k - 1) / |F|`.
  Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.SampleChallenge
public import LeanerVM.Protocol.ToCompPoly.PowerBatching

/-!
# Batching by powers

`batch value out` is the one-challenge component that reduces `k` claimed values to one: the
statement `s` claims the values `value s : Fin k → F`, the verifier draws `ρ`, and the output
statement `out s ρ (Σ_j value_j · ρ^j)` records the challenge and the combined claim
(`powerBatch`). How the output statement records them is the consumer's, so that a protocol that
keeps its own statement types composes with no relabelling step.

Completeness (`batchComplete`): the input relation is carried into the output relation at every
challenge. Knowledge soundness (`batchSecurity`, at `(k - 1) / |F|`, with the extractor that keeps
a witness that carries no information): a statement outside the input relation has true values `a`
different from the claimed ones, fixed before the challenge, and lands in the output relation only
if the combined claim equals the combination of `a`; the difference is a nonzero polynomial of
degree less than `k` in `ρ`, so at most `k - 1` challenges do (`card_false_batch_le`).
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Component

variable {ι : Type} (O : ι → Type) [∀ i, OracleInterface (O i)] {S T W : Type}
  (F : Type) [Field F] [SampleableType F] {k : ℕ} (value : S → Fin k → F) (out : S → F → F → T)

/-- Batching by powers: draw `ρ`, combine the claimed values by its powers. -/
def batch : Def S O W T O W (draw F) :=
  sampleChallenge O F (fun _ ↦ true) fun s ρ ↦ out s ρ (powerBatch (value s) ρ)

variable {relIn : Set ((S × ∀ i, O i) × W)} {relOut : Set ((T × ∀ i, O i) × W)}

/-- Its completeness, whenever the input relation is carried into the output relation at every
challenge. -/
def batchComplete
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ∀ ρ, ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut) :
    Complete (batch O F value out) relIn relOut :=
  sampleChallengeComplete O F _ _ fun s o w hin ↦ ⟨rfl, h s o w hin⟩

variable [Finite F] [DecidableEq F] [Subsingleton W]

/-- Its security at `(k - 1) / |F|`, whenever a statement outside the input relation has values `a`,
fixed before the challenge, such that a challenge carrying it into the output relation makes the
combined claim the combination of `a`, and `a` is not the claimed values. -/
def batchSecurity
    (h : ∀ s o w, ((s, o), w) ∉ relIn → ∃ a : Fin k → F, ∀ ρ,
      ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut →
        a ≠ value s ∧ powerBatch (value s) ρ = powerBatch a ρ) :
    Security (batch O F value out) relIn relOut
      (drawError F (((k - 1 : ℕ) : ℝ≥0) / (Nat.card F : ℝ≥0))) :=
  sampleChallengeSecurity O F _ _ (k - 1) fun s o _ ↦ by
    have := Fintype.ofFinite F
    classical
    rw [natCard_subtype_eq_card_filter]
    by_cases hW : Nonempty W
    · obtain ⟨w⟩ := hW
      by_cases hin : ((s, o), w) ∈ relIn
      · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ρ - ⟨w', hw', -⟩
        exact hw' (Subsingleton.elim w w' ▸ hin)
      · obtain ⟨a, ha⟩ := h s o w hin
        by_cases hgood : ∃ ρ, ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut
        · obtain ⟨ρ₀, hρ₀⟩ := hgood
          refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans
            (card_false_batch_le (value s) a (Function.ne_iff.mp (ha ρ₀ hρ₀).1.symm))
          obtain ⟨w', -, hout⟩ := (Finset.mem_filter.mp hρ).2
          rw [Subsingleton.elim w' w] at hout
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ha ρ hout).2⟩
        · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro ρ - ⟨w', -, hout⟩
          exact hgood ⟨ρ, Subsingleton.elim w' w ▸ hout⟩
    · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ρ - ⟨w, -⟩
      exact hW ⟨w⟩

end Component

end
end LeanerVM.Protocol
