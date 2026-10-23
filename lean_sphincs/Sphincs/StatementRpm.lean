import Sphincs.StatementDet
import LeanRpm.Signature

/-!
# leanSPHINCS security statement in the random-permutation model

The SUF-CMA game of `StatementDet.lean` (the deterministic signer, keys from a uniform 32-byte
seed) with the hash `H` instantiated as Keccak-256 over a uniformly random permutation `π` of the
200-byte Keccak-f[1600] state (`LeanRpm`): `H` is the sponge over `π` (rate 136 bytes, capacity
512 bits, Keccak padding), its 32 output bytes read as the little-endian `HashOutput`
(`LeanRpm.SufCma.digestBitVec`), and the adversary queries Keccak-256, `π` and `π⁻¹` besides the
signing oracle. Key generation, signing and the final verification hash through the same `π`.

The budget counts permutation calls on every path of the game, whatever the answers: a hash of
`n` bytes costs `⌊n / 136⌋ + 1` calls (one per block of the padded message), a query of `π` or
`π⁻¹` one (`LeanRpm.SufCma.permCalls`). The refined statement also counts the calls of `H`, `π`
and `π⁻¹`, one each (`LeanRpm.SufCma.oracleCalls`).
-/

open OracleComp OracleSpec ENNReal LeanRpm LeanRpm.SufCma

namespace Sphincs.Rpm

variable [Params]

/-- leanSPHINCS in the generic SUF-CMA game: the seed, key generation, the deterministic signer,
the verifier, and the winning condition of `StatementDet.lean`. -/
noncomputable def scheme :
    Scheme HashOutput MasterSeed PublicKey Seeded.SecretKey Message (Option Signature)
      Forgery where
  sample := sampleMasterSeed
  keygen := Seeded.keygenFromSeed
  sign sk message := Seeded.sign sk message
  verify pk forgery := Concrete.verify pk forgery.message forgery.signature
  win log forgery :=
    decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery)

/-- An adversary in the random-permutation model: private coins, Keccak-256 (32 bytes), `π`,
`π⁻¹` and the signing oracle. -/
structure Adversary where
  main : PublicKey → OracleComp (KSpec + SigningSpec) Forgery

/-- The game: the seed, key generation, the adversary with the signing oracle, the final
verification, all hashing with Keccak-256 over the permutation. -/
noncomputable def game (adversary : Adversary) : OracleComp KSpec Bool :=
  rpmGame (digestBitVec : KDigest ≃ HashOutput) scheme adversary.main

/-- The probability of a successful forgery against the lazily sampled random permutation. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let b ← rpmExperiment (digestBitVec : KDigest ≃ HashOutput) scheme adversary.main}[b = true]

/-- Every path of the game makes at most `Q` permutation calls, the sponge's included. -/
def HasPermutationBound (adversary : Adversary) (Q : Nat) : Prop :=
  IsWeightBound (game adversary) permCalls Q

/-- Every path of the game makes at most `q` calls of `H`, `π` and `π⁻¹` in all. -/
def HasCallBound (adversary : Adversary) (q : Nat) : Prop :=
  IsWeightBound (game adversary) oracleCalls q

/-- Every adversary whose game makes at most `Q ≥ 1` permutation calls wins with probability at
most `Q / 2^bits + Q² / 2^509`. -/
def HasRpmSecurityBits (bits : Nat) : Prop :=
  ∀ Q, 1 ≤ Q → ∀ adversary, HasPermutationBound adversary Q →
    forgeAdvantage adversary ≤ Q / ((2 ^ bits : Nat) : ℝ≥0∞) + (Q ^ 2 : ℝ≥0∞) / 2 ^ 509

/-- The refined form: every adversary whose game makes at most `q ≥ 1` calls of `H`, `π` and
`π⁻¹` and at most `Q` permutation calls wins with probability at most
`q / 2^bits + Q² / 2^509`. -/
def HasRpmSecurityBitsCalls (bits : Nat) : Prop :=
  ∀ q Q, 1 ≤ q → ∀ adversary, HasCallBound adversary q → HasPermutationBound adversary Q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞) + (Q ^ 2 : ℝ≥0∞) / 2 ^ 509

end Sphincs.Rpm
