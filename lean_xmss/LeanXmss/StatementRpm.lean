import LeanXmss.Statement
import Common.Signature
import Statement.LeanXmss

/-!
# leanXMSS security statement in the random-permutation model

The SUF-CMA game of `Statement.lean` with the hash `H` instantiated as Keccak-256 over a uniformly
random permutation `π` of the 200-byte Keccak-f[1600] state (`Common`): `H` is the sponge over
`π` (rate 136 bytes, capacity 512 bits, Keccak padding), its 32 output bytes read as the
little-endian `HashOutput` (`Common.SufCma.digestBitVec`), and the adversary queries Keccak-256,
`π` and `π⁻¹` besides the signing oracle. Key generation, signing and the final verification hash
through the same `π`.

The budget counts permutation calls on every path of the game, whatever the answers: a hash of
`n` bytes costs `⌊n / 136⌋ + 1` calls (one per block of the padded message), a query of `π` or
`π⁻¹` one (`Common.SufCma.permCalls`). The refined statement also counts the calls of `H`, `π`
and `π⁻¹`, one each (`Common.SufCma.oracleCalls`).
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace LeanXmss.Rpm

/-- Every path of the game makes at most `q` calls of `H`, `π` and `π⁻¹` in all. -/
def HasCallBound (adversary : Adversary) (q : Nat) : Prop :=
  IsWeightBound (game adversary) oracleCalls q

end LeanXmss.Rpm
