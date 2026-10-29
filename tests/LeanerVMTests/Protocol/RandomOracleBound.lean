import LeanerVM.Protocol.RandomOracleBound
import LeanerVMTests.Protocol.ChainGroups

/-!
# The potential of the random-oracle bound: tests

At the toy reader of the chain-group tests (a nonce, then a challenge of one squeeze a proof of
work of one bit precedes, the challenges with a low zero bit bad):

* the potential is `0` at the start, and the step of the potential holds at every fresh query;
* a uniform check passes with probability `1/2` and a uniform challenge is bad with probability
  `1/2`, so a group with no logged query closes on a bad challenge with probability at most
  `1/4` (`π_le_of_not_asked`), the nonce group before its check among them; the bound is one
  draw: the same group once its check passes is bounded by `1/2` only;
* the charge of a query from a clean state within `L` queries is at most
  `(4L + 1) / 2^256 + 1/4`;
* the toy's starts are safe with its seed among the roots and not with no roots, since it
  announces at the empty history; a reader announcing nothing there is safe with no roots.
-/

namespace LeanerVMTests.Protocol.RandomOracleBound

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open OracleComp OracleSpec ProtocolSpec
open LeanerVMTests.Protocol.ChainGroups
open scoped ENNReal

/-- The toy reader from the seed `s₀`. -/
abbrev R : SlotReader := toyReader s₀

-- The potential at the start is `0`.
example : R.Φ [s₀] [] 0 ((∅ : hashSpec.QueryCache), []) = 0 := R.Φ_empty

-- The step of the potential, at every state and fresh query.
example (s : OracleState) (t : List UInt8) (ht : s.1 t = none) :
    ∫⁻ p, p ∂𝒟[(fun u ↦ R.Φ [s₀] [] 0 (QueryHistory.freshLog.record s t u)) <$> ($ᵗ Digest)] ≤
      R.Φ [s₀] [] 0 s + R.charge [s₀] [] 0 s t :=
  R.potential_step s t ht

/-- A uniform digest has a low zero bit with probability `1/2`. -/
theorem half : Pr{let d ← $ᵗ Digest}[FsState.lowBitsZero d 1 = true] = 2⁻¹ := by
  rw [prEvent_lowBitsZero (by norm_num), pow_one]

/-- **The toy's density**, from every seed: a check passes with probability `1/2`, a challenge is
bad with probability `1/2`, so at most `1/4` together. -/
theorem toy_bad (seed : Digest) : (toyReader seed).Density 4⁻¹ := fun _ i _ ↦ by
  obtain rfl := eq_chal i
  show Pr{let d ← $ᵗ Digest}[FsState.lowBitsZero d 1 = true] *
    Pr{let c ← $ᵗ Digest}[FsState.lowBitsZero c 1 = true] ≤ 4⁻¹
  rw [half, ← ENNReal.mul_inv (by simp) (by simp)]
  norm_num

-- The nonce group before its check has no logged query, so it closes on a bad challenge with
-- probability at most `1/4`.
#guard !G₁.asked log₀ (R.size log₀ G₁)
example : R.π log₀ G₁ ≤ 4⁻¹ := R.π_le_of_not_asked (toy_bad s₀) (by decide)

-- Once its check passes, the opening bound no longer applies: the group has a logged query.
#guard G₁.asked log₁ (R.size log₁ G₁)

-- The charge within `L` queries.
example (s : OracleState) (L : ℕ) (hL : s.1.enncard + 1 ≤ L) (t : List UInt8) :
    R.charge [s₀] [] 0 s t ≤ ((4 * L + 1 + 0 : ℕ) : ℝ≥0∞) / 2 ^ 256 + 4⁻¹ :=
  R.charge_le (R.startsSafe_of_seed _ rfl (List.mem_singleton_self _)) (toy_bad s₀) hL t

-- The toy's start is safe among the roots, and not without them: the toy announces at the empty
-- history, so its seed, were it a fresh answer, would open a group that fixes a challenge.
example : R.StartsSafe [s₀] := R.startsSafe_of_seed _ rfl (List.mem_singleton_self _)
example : ¬ R.StartsSafe [] := fun h ↦ by
  rcases h [] s₀ () (ChainStarts.stmtAt_startAt s₀ []) with h | h
  · simp at h
  · exact Option.some_ne_none _ h

/-- The toy reader announcing nothing at the empty history. -/
def lateToy : SlotReader :=
  { R with announcementOf := fun _ hs ↦ if hs.isEmpty then none else some () }

-- A start that announces nothing at the empty history is safe with no roots.
example : lateToy.StartsSafe [] := fun _ _ _ _ ↦ .inr rfl

end LeanerVMTests.Protocol.RandomOracleBound
