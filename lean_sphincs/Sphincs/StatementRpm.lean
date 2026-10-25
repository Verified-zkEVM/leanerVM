import Sphincs.StatementDet
import Common.Signature
import Statement.LeanSphincs

/-!
# leanSPHINCS security statement in the random-permutation model

The SUF-CMA game of `StatementDet.lean` (the deterministic signer, keys from a uniform 32-byte
seed) with the hash `H` instantiated as Keccak-256 over a uniformly random permutation `π` of the
200-byte Keccak-f[1600] state (`Common`): `H` is the sponge over `π` (rate 136 bytes, capacity
512 bits, Keccak padding), its 32 output bytes read as the little-endian `HashOutput`
(`Common.SufCma.digestBitVec`), and the adversary queries Keccak-256, `π` and `π⁻¹` besides the
signing oracle. Key generation, signing and the final verification hash through the same `π`.

The budget counts permutation calls on every path of the game, whatever the answers: a hash of
`n` bytes costs `⌊n / 136⌋ + 1` calls (one per block of the padded message), a query of `π` or
`π⁻¹` one (`Common.SufCma.permCalls`). The refined statement also counts the calls of `H`, `π`
and `π⁻¹`, one each (`Common.SufCma.oracleCalls`).
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace Sphincs.Rpm

variable [Params]

/-- Every path of the game makes at most `q` calls of `H`, `π` and `π⁻¹` in all. -/
def HasCallBound (adversary : Adversary) (q : Nat) : Prop :=
  IsWeightBound (game adversary) oracleCalls q

/-- The refined form: every adversary whose game makes at most `q ≥ 1` calls of `H`, `π` and
`π⁻¹` and at most `Q` permutation calls wins with probability at most
`q / 2^bits + Q² / 2^509`. -/
def HasRpmSecurityBitsCalls (bits : Nat) : Prop :=
  ∀ q Q, 1 ≤ q → ∀ adversary, HasCallBound adversary q → HasPermutationBound adversary Q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞) + (Q ^ 2 : ℝ≥0∞) / 2 ^ 509

end Sphincs.Rpm
