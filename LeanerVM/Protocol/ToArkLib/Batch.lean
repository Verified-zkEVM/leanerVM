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
the witness): a statement has true values `a`, fixed before the challenge and the witness, and
with a witness outside the input relation it lands in the output relation only if `a` differs from
the claimed values and the combined claim equals the combination of `a`; the difference is a
nonzero polynomial of degree less than `k` in `ρ`, so at most `k - 1` challenges do
(`card_false_batch_le`). Fixing `a` before the witness is what keeps the count at `k - 1`: values
depending on the witness would let the bad challenges of different witnesses add up.
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

variable [Finite F]

/-- Its security at `(k - 1) / |F|`, whenever every statement has values `a`, fixed before the
challenge and the witness, such that a challenge carrying it, with a witness outside the input
relation, into the output relation makes the combined claim the combination of `a`, and `a` is
not the claimed values. -/
def batchSecurity
    (h : ∀ s o, ∃ a : Fin k → F, ∀ w ρ, ((s, o), w) ∉ relIn →
      ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut →
        a ≠ value s ∧ powerBatch (value s) ρ = powerBatch a ρ) :
    Security (batch O F value out) relIn relOut
      (drawError F (((k - 1 : ℕ) : ℝ≥0) / (Nat.card F : ℝ≥0))) :=
  sampleChallengeSecurity O F _ _ (k - 1) fun s o _ ↦ by
    have := Fintype.ofFinite F
    classical
    rw [natCard_subtype_eq_card_filter]
    obtain ⟨a, ha⟩ := h s o
    by_cases hgood : ∃ ρ w, ((s, o), w) ∉ relIn ∧
        ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut
    · obtain ⟨ρ₀, w₀, hin₀, hρ₀⟩ := hgood
      refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans
        (card_false_batch_le (value s) a (Function.ne_iff.mp (ha w₀ ρ₀ hin₀ hρ₀).1.symm))
      obtain ⟨w', hw', hout⟩ := (Finset.mem_filter.mp hρ).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ha w' ρ hw' hout).2⟩
    · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ρ - ⟨w', hw', hout⟩
      exact hgood ⟨ρ, w', hw', hout⟩

end Component

end
end LeanerVM.Protocol
