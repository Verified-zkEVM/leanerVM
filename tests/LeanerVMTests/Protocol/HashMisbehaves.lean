import LeanerVM.Protocol.HashMisbehaves
import LeanerVMTests.Protocol.RandomOracleBound

/-!
# The hash misbehaves with small probability: tests

* The error at `2^-128` per challenge, `2^64` prover queries and `2^20` verifier queries is below
  `2^-60`: about `2^-64` for the challenges and `2^-126` for collisions and hits.
* A flip survives deduplication, the step from the game's joint log to the fresh log.
* `misbehaves_rom` at the two-challenge reader of the chain-group tests, whose challenges are never
  bad, a verifier that asks nothing, and proofs with no roots, the reader's seed in play from the
  start: its hypotheses are met, and the bound is one on collisions and hits alone.
* `misbehaves_rom` at the toy reader from the chain's first state, whose bad challenges have
  density `1/4`, and its form for a prover with coins.
* `misbehaves_rom` from no root, at the toy reader announcing nothing at the empty history
  (`lateToy`), whose starts are safe with no root.
-/

namespace LeanerVMTests.Protocol.HashMisbehaves

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol OracleComp
open LeanerVMTests.Protocol.ChainGroups
open scoped NNReal ENNReal

-- The error at `2^-128` per challenge, `2^64` prover queries and `2^20` verifier queries.
example : niError εquery (2 ^ 20) (2 ^ 64) ≤ (2 ^ 60)⁻¹ := by
  rw [← NNReal.coe_le_coe]
  push_cast [niError, hashTerm, εquery]
  norm_num

-- The bound at the two-challenge reader: a verifier asking nothing, proofs with no roots.
example (prog : Program) (input : PublicInput) (A : Adversary) {Q : ℕ}
    (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame (fun _ _ _ _ ↦ pure true) prog input A)}[
      HashMisbehavesFrom [(FsState.seed prog input).cv] (fun _ ↦ [])
        (pairReader (FsState.seed prog input).cv).Flip z.1] ≤
      niError 0 0 Q :=
  misbehaves_rom _ le_rfl (SlotReader.startsSafe_of_seed _ _ rfl (List.mem_singleton_self _))
    (fun _ i _ ↦ by
      simp only [pairReader, pairBad, Bool.false_eq_true, ↓reduceIte, one_mul]
      exact le_of_eq_of_le ((@SampleableType.prEvent_uniformSample_eq_zero_iff _
        (pairSampleable i) _).mpr fun _ hc ↦ hc) zero_le)
    prog input (fun _ _ _ _ ↦ pure true) (fun _ ↦ trivial) (fun _ ↦ [])
    (fun _ ↦ by simp [proofDigests]) A hQ

-- The bound at the toy reader, whose bad challenges have density `1/4`.
example (prog : Program) (input : PublicInput) (A : Adversary) {Q : ℕ}
    (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame (fun _ _ _ _ ↦ pure true) prog input A)}[
      HashMisbehavesFrom [(FsState.seed prog input).cv] (fun _ ↦ [])
        (toyReader (FsState.seed prog input).cv).Flip z.1] ≤
      niError 4⁻¹ 0 Q :=
  misbehaves_rom _ le_rfl (SlotReader.startsSafe_of_seed _ _ rfl (List.mem_singleton_self _))
    (by simpa using RandomOracleBound.toy_bad _) prog input (fun _ _ _ _ ↦ pure true)
    (fun _ ↦ trivial) (fun _ ↦ []) (fun _ ↦ by simp [proofDigests]) A hQ

-- The same for a prover with coins: a uniform choice between two provers.
example (prog : Program) (input : PublicInput) (A₀ A₁ : Adversary) {Q : ℕ}
    (hQ₀ : IsTotalQueryBound A₀ Q) (hQ₁ : IsTotalQueryBound A₁ Q) :
    Pr{let A ← (fun b : Bool ↦ if b then A₁ else A₀) <$> ($ᵗ Bool)
       let z ← runRandom (loggedGame (fun _ _ _ _ ↦ pure true) prog input A)}[
      HashMisbehavesFrom [(FsState.seed prog input).cv] (fun _ ↦ [])
        (toyReader (FsState.seed prog input).cv).Flip z.1] ≤
      niError 4⁻¹ 0 Q :=
  misbehaves_rom_coins _ le_rfl (SlotReader.startsSafe_of_seed _ _ rfl (List.mem_singleton_self _))
    (by simpa using RandomOracleBound.toy_bad _) prog input (fun _ _ _ _ ↦ pure true)
    (fun _ ↦ trivial) (fun _ ↦ []) (fun _ ↦ by simp [proofDigests]) _
    fun A hA ↦ by
      simp only [support_map, Set.mem_image] at hA
      obtain ⟨b, -, rfl⟩ := hA
      cases b
      · exact hQ₀
      · exact hQ₁

-- The bound from no root, at the toy reader announcing nothing at the empty history.
example (prog : Program) (input : PublicInput) (A : Adversary) {Q : ℕ}
    (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame (fun _ _ _ _ ↦ pure true) prog input A)}[
      HashMisbehavesFrom [] (fun _ ↦ []) RandomOracleBound.lateToy.Flip z.1] ≤
      niError 4⁻¹ 0 Q :=
  misbehaves_rom _ (Nat.zero_le _) (fun _ _ _ _ ↦ .inr rfl)
    (by simpa using show RandomOracleBound.lateToy.Density 4⁻¹ from RandomOracleBound.toy_bad s₀)
    prog input (fun _ _ _ _ ↦ pure true) (fun _ ↦ trivial) (fun _ ↦ [])
    (fun _ ↦ by simp [proofDigests]) A hQ

-- Deduplication keeps a flip: the toy's flipping log, asked twice, deduplicates to itself.
#guard List.dedupKeys (log₃ ++ log₃) = log₃
example : R.FlipAt (List.dedupKeys log₃) := R.flipAt_dedupKeys (by decide) ⟨G₁, flips₃⟩

end LeanerVMTests.Protocol.HashMisbehaves
