import Sphincs.StatementDet
import Common.Signature
import Common.PiOnly
import Common.Linear
import Sphincs.Layered
import Common.WithHash

/-!
# leanSPHINCS security statement in the random-permutation model

The SUF-CMA game of `StatementDet.lean` (the deterministic signer, keys from a uniform 32-byte
seed) with the hash `H` instantiated as Keccak-256 over a uniformly random permutation `π` of the
Keccak-f[1600] state of 25 lanes (`Common`): `H` is the sponge over `π` (rate 136 bytes, capacity
512 bits, Keccak padding), its 32 output bytes read as the little-endian `HashOutput`
(`Common.SufCma.digestBitVec`), and the adversary queries Keccak-256, `π` and `π⁻¹` besides the
signing oracle (the model with the hash oracle, `Common.HashOracle`; the statement's adversary
queries `π` and `π⁻¹` alone, `Common.PiOnly`). Key generation, signing and the final verification
hash through the same `π`.

The budget counts permutation calls on every path of the game, whatever the answers: a hash of
`n` bytes costs `⌊n / 136⌋ + 1` calls (one per block of the padded message), a query of `π` or
`π⁻¹` one (`Common.permCallsH`). The refined statement also counts the calls of `H`, `π`
and `π⁻¹`, one each (`Common.SufCma.oracleCalls`).
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace SphincsLayered.Rpm

variable [Params]

/-- An adversary in the random-permutation model: private coins, Keccak-256 (32 bytes), `π`,
`π⁻¹` and the signing oracle. -/
structure Adversary where
  main : PublicKey → OracleComp (KSpecH + SigningSpec) Forgery

/-- The game: the seed, key generation, the adversary with the signing oracle, the final
verification, all hashing with Keccak-256 over the permutation. -/
noncomputable def game (adversary : Adversary) : OracleComp KSpecH Bool :=
  rpmGameH scheme adversary.main

/-- The probability of a successful forgery against the lazily sampled random permutation. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let b ← rpmExperimentH scheme adversary.main}[b = true]

/-- Every path of the game makes at most `Q` permutation calls, the sponge's included. -/
def HasPermutationBound (adversary : Adversary) (Q : Nat) : Prop :=
  QueryCostAtMost (game adversary) permCallsH Q

/-- Every adversary whose game makes at most `Q` permutation calls, `1 ≤ Q ≤ 2^128`, wins with
probability at most `(Q + 1) · 2^-bits`. -/
def HasRpmSecurityBits (bits : Nat) : Prop :=
  ∀ Q, 1 ≤ Q → Q ≤ 2 ^ 128 → ∀ adversary, HasPermutationBound adversary Q →
    forgeAdvantage adversary ≤ ((Q : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ bits

/- A weight bound of a concrete game must not be unfolded: it recurses through the whole game. -/
attribute [local irreducible] QueryCostAtMost in
/-- `HasRpmSecurityBits` gives the statement's `StronglyUnforgeable`, whose bound is at least one past
`Q = 2^128` for `bits ≤ 128`: first against adversaries that also query Keccak-256, then against
the statement's, which query `π` and `π⁻¹` alone (`Common.SufCma.rpmSecure_of_rpmSecureH`). -/
theorem rpmSecure_of_bits {bits : Nat} (h : HasRpmSecurityBits bits) (hb : bits ≤ 128) :
    StronglyUnforgeableWithHash scheme bits := by
  refine rpmSecure_of_rpmSecureH ?_
  intro Q hQ main hbound
  rcases le_or_gt Q (2 ^ 128) with hcap | hcap
  · exact h Q hQ hcap ⟨main⟩ hbound
  · exact Common.le_succ_mul_inv_two_pow_of_lt (prEvent_le_one _) hb hcap

/-- Every path of the game makes at most `q` calls of `H`, `π` and `π⁻¹` in all. -/
def HasCallBound (adversary : Adversary) (q : Nat) : Prop :=
  QueryCostAtMost (game adversary) oracleCalls q

/-- The refined form: every adversary whose game makes at most `q ≥ 1` calls of `H`, `π` and
`π⁻¹` and at most `Q` permutation calls wins with probability at most
`q / 2^bits + Q² / 2^509`. -/
def HasRpmSecurityBitsCalls (bits : Nat) : Prop :=
  ∀ q Q, 1 ≤ q → ∀ adversary, HasCallBound adversary q → HasPermutationBound adversary Q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞) + (Q ^ 2 : ℝ≥0∞) / 2 ^ 509

end SphincsLayered.Rpm
