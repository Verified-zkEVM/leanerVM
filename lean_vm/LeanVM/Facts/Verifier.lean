/-
  LeanVM.Facts.Verifier

  Facts about the verifier's definitions (`Statement/LeanVmVerifier.lean`), proved:
  the `q_keccak` spare slots and the `KECCAK` slot layout, and `pack`; and the verifier's
  definitions no end statement reaches, moved here from the statement, names kept: `yE`,
  `keccakOut`, `packBits`, `pack`, the deployed seed `seed` and the deployed verifier `verify`.
-/

module

public import Statement.Field
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import Statement.Fast.Keccak
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Statement.LeanVmVerifier

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The guard of `verifier.py:951` (an `assert` when the module loads): every spare slot of
`q_keccak` has a committed `KECCAK` column to carry. -/
theorem qkeccakSpare_le_length_keccakCommitted : qkeccakSpare ≤ keccakCommitted.length := by
  decide +kernel

/-- The two parts of `KECCAK_SLOT_OF` have disjoint keys: no spare-carrying committed column is an
input lane. -/
theorem keccakSlotOf_disjoint :
    ∀ l ∈ keccakCommitted.take qkeccakSpare, ¬ (keccakIn ≤ l ∧ l < keccakIn + 25) := by
  decide +kernel

open LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

/-- `E(0, 1)`, the tower generator `y` with `y^3 = y + 1`. -/
def yE : E := E.ofLimbs 0 1 0

/-- `KECCAK_OUT` (`verifier.py:942`): the local column of output lane `0`. -/
def keccakOut : ℕ := colIdx keccakColumns "out_0"

/-- `PACK_BITS` (`verifier.py:1224`): a pack is `2 ^ PACK_BITS` consecutive steps. -/
def packBits : ℕ := 4

/-- The steps of a pack, `2 ^ PACK_BITS = 16`. -/
def pack : ℕ := 16

theorem pack_eq : pack = 2 ^ packBits := rfl

/-- The deployed seed, with Keccak. -/
def seed (bytecode : List K) (publicInput : Digest) : KeccakState :=
  Id.run (seedWith (m := Id) keccak256 keccakF1600 bytecode publicInput)

/-- **The deployed leanVM verifier**: the program's compiled reading with Keccak-256 and
Keccak-f[1600], from the deployed seed. -/
def verify (bytecode : List K) (publicInput : Digest) (π : Proof) : Bool :=
  Id.run (runProof (m := Id) keccak256 keccakF1600 (leanVmProgram bytecode publicInput)
    (seed bytecode publicInput) π)

end
end LeanVM.Protocol.Verifier
