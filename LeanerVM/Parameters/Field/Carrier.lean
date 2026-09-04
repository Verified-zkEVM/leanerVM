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

/-- Distinct carrier values denote distinct quotient elements.

A difference of two carrier values has degree below 64, while the modulus has degree
exactly 64, so the modulus can divide it only when it is zero. -/
theorem toQuot_injective : Function.Injective toQuot := by
  intro a b h
  have hsub : toPolyBase a - toPolyBase b = toPoly (a ^^^ b) := by
    rw [toPoly_xor, toPolyBase, toPolyBase]
    exact ZMod2Poly.sub_eq_add _ _
  have hdvd : basePoly ∣ toPolyBase a - toPolyBase b := AdjoinRoot.mk_eq_mk.mp h
  have hzero : toPoly (a ^^^ b) = 0 := by
    by_contra hnz
    have hne : toPolyBase a - toPolyBase b ≠ 0 := by rw [hsub]; exact hnz
    have hle := Polynomial.degree_le_of_dvd hdvd hne
    rw [hsub, basePoly_degree] at hle
    exact absurd (toPoly_degree_lt_w (w := 64) (by norm_num) (a ^^^ b)) (not_lt.mpr hle)
  have hxor : (a ^^^ b : BitVec 64) = 0 := by
    by_contra hnz
    exact ((toPoly_ne_zero_iff_ne_zero (a ^^^ b)).mpr hnz) hzero
  have : a = b := by
    have := congrArg (fun v => v ^^^ b) hxor
    simpa [BitVec.xor_assoc] using this
  exact this

/-! ## Algebraic structure

Every law is discharged by pushing through the injective `toQuot` into the quotient,
where it holds because `AdjoinRoot basePoly` is a commutative ring. The instances are
built field-by-field rather than by `Function.Injective.commRing`, because that transport
takes `toQuot` as data and would make the operations noncomputable.
-/

@[simp] theorem toPolyBase_one : toPolyBase 1 = 1 :=
  toPoly_one_eq_one (w := 64) (by norm_num)

@[simp] theorem toQuot_one : toQuot 1 = 1 := by
  rw [toQuot, toPolyBase_one, map_one]

theorem toQuot_inj {a b : Base} : toQuot a = toQuot b ↔ a = b :=
  ⟨fun h => toQuot_injective h, fun h => h ▸ rfl⟩

/-- Addition is self-cancelling: the field has characteristic two. -/
theorem add_self (a : Base) : a + a = 0 := BitVec.xor_self

/-! ### Scalar and power operations

In characteristic two an integer scalar multiple collapses to a parity test, and the
natural- and integer-number casts collapse likewise. Defining them in that closed form
keeps them computable and makes the transport conditions immediate.
-/

instance : SMul ℕ Base := ⟨fun n a => if n % 2 = 0 then 0 else a⟩
instance : SMul ℤ Base := ⟨fun n a => if n % 2 = 0 then 0 else a⟩
instance : NatCast Base := ⟨fun n => if n % 2 = 0 then 0 else 1⟩
instance : IntCast Base := ⟨fun n => if n % 2 = 0 then 0 else 1⟩
instance : Pow Base ℕ := ⟨fun a n => npowRec n a⟩

theorem nsmul_def (n : ℕ) (a : Base) : n • a = if n % 2 = 0 then 0 else a := rfl
theorem zsmul_def (n : ℤ) (a : Base) : n • a = if n % 2 = 0 then 0 else a := rfl
theorem natCast_def (n : ℕ) : (n : Base) = if n % 2 = 0 then 0 else 1 := rfl
theorem intCast_def (n : ℤ) : (n : Base) = if n % 2 = 0 then 0 else 1 := rfl
theorem npow_def (a : Base) (n : ℕ) : a ^ n = npowRec n a := rfl

/-! ### The commutative-ring structure

Every law is transported along the injective `toQuot` from `AdjoinRoot basePoly`. The
transport takes `toQuot` as data, so the resulting structure is noncomputable; the
computable operations remain reachable through `add_def`, `mul_def`, and the equation
lemmas above, and `toQuot_add` / `toQuot_mul` connect the two views.
-/

theorem toQuot_neg (a : Base) : toQuot (-a) = -toQuot a := by
  show toQuot a = -toQuot a
  rw [eq_neg_iff_add_eq_zero, ← toQuot_add, add_self, toQuot_zero]

theorem toQuot_sub (a b : Base) : toQuot (a - b) = toQuot a - toQuot b := by
  show toQuot (a + b) = toQuot a - toQuot b
  rw [toQuot_add, sub_eq_add_neg]
  congr 1
  rw [← toQuot_neg b]
  rfl

/-- The quotient inherits characteristic two from `GF(2)`. -/
instance : CharP (AdjoinRoot basePoly) 2 := by
  have : CharP (ZMod 2) 2 := inferInstance
  exact charP_of_injective_algebraMap' (ZMod 2) 2

/-- Two vanishes in the quotient. -/
private theorem quot_two_eq_zero : (2 : AdjoinRoot basePoly) = 0 := by
  simpa using CharP.cast_eq_zero (AdjoinRoot basePoly) 2

theorem toQuot_nsmul (n : ℕ) (a : Base) : toQuot (n • a) = n • toQuot a := by
  rw [nsmul_def, nsmul_eq_mul]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    rw [if_pos (by omega), toQuot_zero, hk]
    simp [← two_mul, Nat.cast_mul, quot_two_eq_zero]
  · obtain ⟨k, hk⟩ := ho
    rw [if_neg (by omega), hk]
    simp [Nat.cast_add, Nat.cast_mul, quot_two_eq_zero]

theorem toQuot_zsmul (n : ℤ) (a : Base) : toQuot (n • a) = n • toQuot a := by
  rw [zsmul_def, zsmul_eq_mul]
  rcases Int.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    rw [if_pos (by omega), toQuot_zero, hk]
    simp [← two_mul, Int.cast_mul, quot_two_eq_zero]
  · obtain ⟨k, hk⟩ := ho
    rw [if_neg (by omega), hk]
    simp [Int.cast_add, Int.cast_mul, quot_two_eq_zero]

theorem toQuot_npow (a : Base) (n : ℕ) : toQuot (a ^ n) = toQuot a ^ n := by
  induction n with
  | zero => rw [npow_def, npowRec, pow_zero, toQuot_one]
  | succ k ih => rw [npow_def, npowRec, ← npow_def, toQuot_mul, ih, pow_succ]

theorem toQuot_natCast (n : ℕ) : toQuot (n : Base) = (n : AdjoinRoot basePoly) := by
  rw [natCast_def]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    rw [if_pos (by omega), toQuot_zero, hk]
    simp [← two_mul, Nat.cast_mul, quot_two_eq_zero]
  · obtain ⟨k, hk⟩ := ho
    rw [if_neg (by omega), toQuot_one, hk]
    simp [Nat.cast_add, Nat.cast_mul, quot_two_eq_zero]

theorem toQuot_intCast (n : ℤ) : toQuot (n : Base) = (n : AdjoinRoot basePoly) := by
  rw [intCast_def]
  rcases Int.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    rw [if_pos (by omega), toQuot_zero, hk]
    simp [← two_mul, Int.cast_mul, quot_two_eq_zero]
  · obtain ⟨k, hk⟩ := ho
    rw [if_neg (by omega), toQuot_one, hk]
    simp [Int.cast_add, Int.cast_mul, quot_two_eq_zero]

/-- The commutative-ring structure on the carrier, transported along `toQuot`. -/
noncomputable instance : CommRing Base :=
  Function.Injective.commRing toQuot toQuot_injective
    toQuot_zero toQuot_one toQuot_add toQuot_mul toQuot_neg toQuot_sub
    toQuot_nsmul toQuot_zsmul toQuot_npow toQuot_natCast toQuot_intCast

/-! ### The field structure

`AdjoinRoot basePoly` is a field because `basePoly` is irreducible, and `toQuot` is an
injective ring homomorphism onto it, so the carrier is a field too. Following
`CompPoly.Fields.Binary.BF128Ghash`, the structure is packaged as `IsField` and converted,
which elaborates far faster than assembling `Field` by hand on a bit-vector carrier.
-/

theorem toQuot_eq_zero_iff {a : Base} : toQuot a = 0 ↔ a = 0 := by
  rw [← toQuot_zero]
  exact ⟨fun h => toQuot_injective h, fun h => h ▸ rfl⟩

theorem exists_pair_ne : ∃ x y : Base, x ≠ y :=
  ⟨0, 1, by decide +kernel⟩

/-- The carrier is in bijection with `Fin (2 ^ 64)`, by its underlying representation. -/
def equivFin : Base ≃ Fin (2 ^ 64) where
  toFun a := a.toFin
  invFun i := BitVec.ofFin i
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Base := Fintype.ofEquiv _ equivFin.symm

theorem card_base : Fintype.card Base = 2 ^ 64 := by
  rw [Fintype.card_congr equivFin, Fintype.card_fin]

/-- The bridge is surjective: it is injective between finite types of equal cardinality. -/
theorem toQuot_surjective : Function.Surjective toQuot := by
  have hcard : Fintype.card Base = Fintype.card (AdjoinRoot basePoly) := by
    rw [card_base, card_K]
  exact ((Fintype.bijective_iff_injective_and_card toQuot).mpr ⟨toQuot_injective, hcard⟩).2

/-- Every nonzero carrier value has a multiplicative inverse. -/
theorem exists_mul_inv {a : Base} (h : a ≠ 0) : ∃ b : Base, a * b = 1 := by
  have hq : toQuot a ≠ 0 := fun hz => h (toQuot_eq_zero_iff.mp hz)
  obtain ⟨b, hb⟩ := toQuot_surjective (toQuot a)⁻¹
  exact ⟨b, toQuot_injective (by rw [toQuot_mul, hb, toQuot_one, mul_inv_cancel₀ hq])⟩

theorem isField_base : IsField Base where
  exists_pair_ne := exists_pair_ne
  mul_comm := mul_comm
  mul_inv_cancel := fun h => exists_mul_inv h

/-- The carrier is a field: `K = GF(2^64)`. -/
noncomputable instance : Field Base := isField_base.toField

end Base

end
end LeanerVM.Parameters.Field
