import LeanXmss.Statement
import Common.Signature
import Statement.LeanXmss

/-!
# leanXMSS security statement in the random-permutation model

The SUF-CMA game of `Statement.lean` with the hash `H` instantiated as Keccak-256 over a uniformly
random permutation `π` of the Keccak-f[1600] state of 25 lanes (`Common`): `H` is the sponge over
`π` (rate 136 bytes, capacity 512 bits, Keccak padding), its 32 output bytes read as the
little-endian `HashOutput` (`Common.SufCma.digestBitVec`), and the adversary queries Keccak-256,
`π` and `π⁻¹` besides the signing oracle (the model with the hash oracle, `Common.HashOracle`; the
statement's adversary queries `π` and `π⁻¹` alone, `Common.PiOnly`). Key generation, signing and
the final verification hash through the same `π`.

The budget counts permutation calls on every path of the game, whatever the answers: a hash of
`n` bytes costs `⌊n / 136⌋ + 1` calls (one per block of the padded message), a query of `π` or
`π⁻¹` one (`Common.permCallsH`). The refined statement also counts the calls of `H`, `π`
and `π⁻¹`, one each (`Common.SufCma.oracleCalls`).
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace LeanXmss.Rpm

/-- An adversary in the random-permutation model: private coins, Keccak-256 (32 bytes), `π`,
`π⁻¹` and the signing oracle. -/
structure Adversary where
  main : PublicKey → OracleComp (KSpecH + SigningSpec) Forgery

/-- The game: the master seed, key generation, the adversary with the signing oracle, the final
verification, all hashing with Keccak-256 over the permutation. -/
noncomputable def game (adversary : Adversary) : OracleComp KSpecH Bool :=
  rpmGameH scheme adversary.main

/-- The probability of a successful forgery against the lazily sampled random permutation. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let b ← rpmExperimentH scheme adversary.main}[b = true]

/-- Every path of the game makes at most `Q` permutation calls, the sponge's included. -/
def HasPermutationBound (adversary : Adversary) (Q : Nat) : Prop :=
  QueryCostAtMost (game adversary) permCallsH Q

/-- Every path of the game makes at most `q` calls of `H`, `π` and `π⁻¹` in all. -/
def HasCallBound (adversary : Adversary) (q : Nat) : Prop :=
  QueryCostAtMost (game adversary) oracleCalls q

end LeanXmss.Rpm
