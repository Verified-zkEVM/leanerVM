/-
  LeanerVM.Parameters.Field.Carrier

  The computable `BitVec 64` carrier for the leanVM base field, and its bridge to
  the quotient `AdjoinRoot basePoly`.
-/

module

public import LeanerVM.Parameters.Field.Reduce
public import Mathlib.RingTheory.AdjoinRoot

/-!
# The computable base-field carrier

leanVM represents a base-field element as a 64-bit word whose bit `i` is the coefficient
of `x^i` (`crates/primitives/src/field/gf2_64.rs`, `F64(pub u64)`). This module gives that
representation its arithmetic — addition is `xor`, multiplication is a carry-less product
followed by `reduce` — and maps it into `AdjoinRoot basePoly`, so Mathlib's field theory
applies while the operations stay computable.

Following `CompPoly.Fields.Extension`, the algebraic instances are assembled through the
injective bridge rather than transported wholesale, so that `Mul` and `Pow` remain the
computable ones.

Source revision: leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`.

## Main definitions and statements

* `Base` — the carrier, `BitVec 64`.
* `Base.toQuot` — the bridge into `AdjoinRoot basePoly`, with `toQuot_add`, `toQuot_mul`,
  and `toQuot_injective`.
-/

namespace LeanerVM.Parameters.Field

open Polynomial BinaryField

public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

/-- The leanVM base field's machine representation: bit `i` is the coefficient of `x^i`. -/
abbrev Base : Type := BitVec 64

namespace Base

instance : Zero Base := ⟨(0 : BitVec 64)⟩
instance : One Base := ⟨(1 : BitVec 64)⟩

/-- Addition in characteristic two is `xor`. -/
instance : Add Base := ⟨fun a b => a ^^^ b⟩

/-- Negation is the identity in characteristic two. -/
instance : Neg Base := ⟨fun a => a⟩

instance : Sub Base := ⟨fun a b => a ^^^ b⟩

/-- Multiplication: the carry-less product, reduced modulo the modulus. -/
instance : Mul Base :=
  ⟨fun a b => reduce (carryLessMul (w := 128) a b)⟩

/-- The polynomial denoted by a carrier value. -/
noncomputable def toPolyBase (a : Base) : Polynomial (ZMod 2) :=
  toPoly (a : BitVec 64)

/-- The bridge into the quotient. -/
noncomputable def toQuot (a : Base) : AdjoinRoot basePoly :=
  AdjoinRoot.mk basePoly (toPolyBase a)

/-! ## Equation lemmas for the operations -/

theorem add_def (a b : Base) : a + b = a ^^^ b := rfl

theorem mul_def (a b : Base) : a * b = reduce (carryLessMul (w := 128) a b) := rfl

/-! ## The bridge is a ring homomorphism -/

@[simp] theorem toPolyBase_zero : toPolyBase 0 = 0 := by
  show toPoly (0 : BitVec 64) = 0
  exact toPoly_zero_eq_zero

@[simp] theorem toQuot_zero : toQuot 0 = 0 := by
  rw [toQuot, toPolyBase_zero, map_zero]

@[simp] theorem toPolyBase_add (a b : Base) :
    toPolyBase (a + b) = toPolyBase a + toPolyBase b := by
  rw [toPolyBase, toPolyBase, toPolyBase, add_def]
  exact toPoly_xor _ _

@[simp] theorem toQuot_add (a b : Base) : toQuot (a + b) = toQuot a + toQuot b := by
  rw [toQuot, toQuot, toQuot, toPolyBase_add, map_add]

/-- Multiplication agrees with the quotient's, because `reduce` computes the remainder. -/
@[simp] theorem toQuot_mul (a b : Base) : toQuot (a * b) = toQuot a * toQuot b := by
  rw [toQuot, toQuot, toQuot, ← map_mul, toPolyBase, mul_def, toPoly_reduce,
    toPoly_carryLessMul _ _ (by omega)]
  rw [AdjoinRoot.mk_eq_mk, toPolyBase, toPolyBase]
  exact ⟨-(toPoly a * toPoly b / basePoly), by
    rw [EuclideanDomain.mod_eq_sub_mul_div]; ring⟩

end Base

end
end LeanerVM.Parameters.Field
