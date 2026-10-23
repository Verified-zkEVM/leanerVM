import LeanerVM.Protocol.HashMisbehaves
import LeanerVMTests.Protocol.ChainGroups

/-!
# The hash misbehaves with small probability: tests

* The error at `2^64` prover queries and `2^20` verifier queries is below `2^-60`: about `2^-64`
  for the challenges and `2^-126` for collisions and hits.
* A flip survives deduplication, the step from the game's joint log to the fresh log.
* `misbehaves_rom` at the two-challenge reader of the chain-group tests, whose challenges are never
  bad, a verifier that asks nothing, and proofs with no roots: its hypotheses are met, and the
  bound is one on collisions and hits alone.
-/

namespace LeanerVMTests.Protocol.HashMisbehaves

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol OracleComp
open LeanerVMTests.Protocol.ChainGroups
open scoped NNReal ENNReal

-- The error at `2^64` prover queries and `2^20` verifier queries.
example : niError (2 ^ 20) (2 ^ 64) ≤ (2 ^ 60)⁻¹ := by
  rw [← NNReal.coe_le_coe]
  push_cast [niError, hashTerm, εquery]
  norm_num

-- The bound at the two-challenge reader: a verifier asking nothing, proofs with no roots.
example (prog : Program) (input : PublicInput) (A : Adversary) {Q : ℕ}
    (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame (fun _ _ _ _ ↦ pure true) prog input A)}[
      HashMisbehaves (fun _ ↦ []) (pairReader (FsState.seed prog input).cv).Flip prog input z.1] ≤
      niError 0 Q :=
  misbehaves_rom _ prog input (by simp [seedDigests, pairReader])
    (fun _ i _ ↦ by
      simp only [pairReader, pairBad, Bool.false_eq_true, ↓reduceIte, one_mul]
      exact le_of_eq_of_le ((@SampleableType.prEvent_uniformSample_eq_zero_iff _
        (pairSampleable i) _).mpr fun _ hc ↦ hc) zero_le)
    (fun _ _ _ _ ↦ pure true) (fun _ ↦ trivial) (fun _ ↦ []) (fun _ ↦ by simp [proofDigests])
    A hQ

-- Deduplication keeps a flip: the toy's flipping log, asked twice, deduplicates to itself.
#guard List.dedupKeys (log₃ ++ log₃) = log₃
example : R.FlipAt (List.dedupKeys log₃) := R.flipAt_dedupKeys (by decide) ⟨G₁, flips₃⟩

end LeanerVMTests.Protocol.HashMisbehaves
