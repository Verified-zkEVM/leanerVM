/-
  LeanVM.Facts.Verifier

  Facts about the verifier's definitions (`Statement/LeanVmVerifier.lean`), proved:
  the `q_keccak` spare slots and the `KECCAK` slot layout, and `pack`.
  The definitions are the statement's; these are proofs.
-/

module

public import Statement.Field
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import Statement.Fast.Keccak
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Statement.LeanVmVerifier

namespace LeanVM.Parameters.Whir

@[expose] public section

end
end LeanVM.Parameters.Whir

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash

@[expose] public section

end
end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The guard of `verifier.py:950` (an `assert` when the module loads): every spare slot of
`q_keccak` has a committed `KECCAK` column to carry. -/
theorem qkeccakSpare_le_length_keccakCommitted : qkeccakSpare ≤ keccakCommitted.length := by
  decide +kernel

/-- The two parts of `KECCAK_SLOT_OF` have disjoint keys: no spare-carrying committed column is an
input lane. -/
theorem keccakSlotOf_disjoint :
    ∀ l ∈ keccakCommitted.take qkeccakSpare, ¬ (keccakIn ≤ l ∧ l < keccakIn + 25) := by
  decide +kernel

open LeanVM.Protocol.Compile

theorem pack_eq : pack = 2 ^ packBits := rfl

open LeanVM.Semantics LeanVM.Protocol.KeccakHash

end
end LeanVM.Protocol.Verifier
