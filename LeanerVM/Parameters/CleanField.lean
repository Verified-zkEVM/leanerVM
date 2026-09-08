/-
  LeanerVM.Parameters.CleanField

  Clean's field interface for `K`. A plain (non-`module`) file: Clean at `93c9d1ef` is not
  written with Lean's module system, and a `module` may not import a non-`module`.
-/

import LeanerVM.Parameters.Field
import Clean.Utils.FiniteField

/-!
# Clean's field interface for `K`

leanISA roadmap Layer 0 (`docs/roadmap/leanisa-blueprint.md`). `instFiniteFieldK` supplies
Clean's `FiniteField K`, the interface every Clean circuit, table, and channel is generic over,
with `val = BitVec.toNat`, `fromNat = BitVec.ofNat 64`, and `size = 2^64`. The roadmap's
dependency table records that Clean's core never consumes `val` or `size`; only its witness-IR
bridge does, and for a 64-bit field its `UInt64` truncation is the identity.

`instFiniteFieldK_toField` records that the interface's field structure is CompPoly's by `rfl`,
so `K` has one field structure. Clean's `FiniteField.toField` is itself an instance, so
`tests/LeanerVMTests/Parameters/CleanField.lean` guards that instance search for `Field K` still
lands on CompPoly's.

This file is plain rather than a `module` (roadmap status finding C8, settled by the roadmap's
module-system convention), so it lives apart from `LeanerVM.Parameters.Field`, which stays a
`module` for the Semantics layer. Everything importing this file is plain too: `LeanerVM.lean`
and the test aggregate.
-/

namespace LeanerVM.Parameters

/-- Clean's `FiniteField K`: `val` is the word's value and `fromNat` its inverse below `2^64`. -/
instance instFiniteFieldK : FiniteField K where
  val := BitVec.toNat
  fromNat n := BitVec.ofNat 64 n
  size := 2 ^ 64
  val_lt x := x.isLt
  val_injective := fun _ _ h ↦ BitVec.eq_of_toNat_eq h
  val_fromNat n hn := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  val_zero := rfl
  val_one := rfl

/-- The interface introduces no second field structure: its `Field K` is CompPoly's. -/
theorem instFiniteFieldK_toField : (instFiniteFieldK.toField : Field K) = BF64.instField := rfl

end LeanerVM.Parameters
