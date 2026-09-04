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

instance : SMul ℕ Base := ⟨nsmulRec⟩
instance : SMul ℤ Base := ⟨zsmulRec nsmulRec⟩
instance : NatCast Base := ⟨Nat.unaryCast⟩
instance : IntCast Base := ⟨Int.castDef⟩
instance : Pow Base ℕ := ⟨fun a n => npowRec n a⟩

theorem npow_def (a : Base) (n : ℕ) : a ^ n = npowRec n a := rfl

/-! ### The commutative-ring structure

Every law is discharged by pushing through the injective `toQuot` into `AdjoinRoot basePoly`,
where it holds because the quotient is a commutative ring. The instances are written out
field-by-field rather than via `Function.Injective.commRing`: that transport takes `toQuot`
as *data*, which would make the whole structure noncomputable and shadow the computable
operations. This mirrors `CompPoly.Extension.Ext.instCommRing`.
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

instance : AddCommGroup Base where
  add_assoc a b c := toQuot_injective (by simp only [toQuot_add, add_assoc])
  zero_add a := toQuot_injective (by simp only [toQuot_add, toQuot_zero, zero_add])
  add_zero a := toQuot_injective (by simp only [toQuot_add, toQuot_zero, add_zero])
  add_comm a b := toQuot_injective (by simp only [toQuot_add, add_comm])
  neg_add_cancel a :=
    toQuot_injective (by simp only [toQuot_add, toQuot_neg, toQuot_zero, neg_add_cancel])
  sub_eq_add_neg a b :=
    toQuot_injective (by simp only [toQuot_sub, toQuot_add, toQuot_neg, sub_eq_add_neg])
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  zsmul := zsmulRec nsmulRec
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl

theorem toQuot_npow (a : Base) (n : ℕ) : toQuot (a ^ n) = toQuot a ^ n := by
  induction n with
  | zero => rw [npow_def, npowRec, pow_zero, toQuot_one]
  | succ k ih => rw [npow_def, npowRec, ← npow_def, toQuot_mul, ih, pow_succ]

/-- The quotient inherits characteristic two from `GF(2)`. -/
instance : CharP (AdjoinRoot basePoly) 2 := by
  have : CharP (ZMod 2) 2 := inferInstance
  exact charP_of_injective_algebraMap' (ZMod 2) 2

theorem toQuot_natCast (n : ℕ) : toQuot (n : Base) = (n : AdjoinRoot basePoly) := by
  induction n with
  | zero => show toQuot 0 = _; rw [toQuot_zero, Nat.cast_zero]
  | succ k ih =>
    show toQuot ((k : Base) + 1) = _
    rw [toQuot_add, ih, toQuot_one, Nat.cast_succ]

instance : CommRing Base where
  left_distrib a b c := toQuot_injective (by simp only [toQuot_mul, toQuot_add, mul_add])
  right_distrib a b c := toQuot_injective (by simp only [toQuot_mul, toQuot_add, add_mul])
  zero_mul a := toQuot_injective (by simp only [toQuot_mul, toQuot_zero, zero_mul])
  mul_zero a := toQuot_injective (by simp only [toQuot_mul, toQuot_zero, mul_zero])
  mul_assoc a b c := toQuot_injective (by simp only [toQuot_mul, mul_assoc])
  one_mul a := toQuot_injective (by simp only [toQuot_mul, toQuot_one, one_mul])
  mul_one a := toQuot_injective (by simp only [toQuot_mul, toQuot_one, mul_one])
  mul_comm a b := toQuot_injective (by simp only [toQuot_mul, mul_comm])
  npow n x := x ^ n
  npow_zero x := toQuot_injective (by simp only [toQuot_npow, toQuot_one, pow_zero])
  npow_succ n x := toQuot_injective (by simp only [toQuot_npow, toQuot_mul, pow_succ])
  natCast n := (n : Base)
  natCast_zero := toQuot_injective (by simp only [toQuot_natCast, toQuot_zero, Nat.cast_zero])
  natCast_succ n :=
    toQuot_injective (by simp only [toQuot_natCast, toQuot_add, toQuot_one, Nat.cast_succ])
  intCast n := (n : Base)
  intCast_ofNat n := rfl
  intCast_negSucc n := rfl

/-! ### Inversion by Itoh-Tsujii

The pinned Rust inverts in `K` by Itoh-Tsujii (`crates/primitives/src/field/gf2_64.rs`):
`a⁻¹ = a^(2^64 - 2) = (a^(2^63 - 1))^2`, with `a^(2^k - 1)` built by the addition chain
`1, 2, 3, 6, 7, 14, 15, 30, 31, 62, 63`. This is an explicit algorithm rather than an
existence proof, so the resulting inverse evaluates.
-/

/-- Repeated squaring: `a ^ (2 ^ k)`. -/
@[expose] def powTwoPow (a : Base) (k : ℕ) : Base :=
  match k with
  | 0 => a
  | n + 1 => powTwoPow (a * a) n

theorem toQuot_powTwoPow (a : Base) (k : ℕ) :
    toQuot (powTwoPow a k) = toQuot a ^ (2 ^ k) := by
  induction k generalizing a with
  | zero => simp only [powTwoPow, pow_zero, pow_one]
  | succ n ih =>
    simp only [powTwoPow]
    rw [ih, toQuot_mul, ← sq, ← pow_mul, pow_succ, mul_comm]

/-- The multiplicative inverse, by the Itoh-Tsujii addition chain. `0⁻¹ = 0`, matching the
pinned Rust's convention. -/
@[expose] def invItohTsujii (a : Base) : Base :=
  if a = 0 then 0 else
    let u1 := a
    let u2 := powTwoPow u1 1 * u1
    let u3 := powTwoPow u2 1 * u1
    let u6 := powTwoPow u3 3 * u3
    let u7 := powTwoPow u6 1 * u1
    let u14 := powTwoPow u7 7 * u7
    let u15 := powTwoPow u14 1 * u1
    let u30 := powTwoPow u15 15 * u15
    let u31 := powTwoPow u30 1 * u1
    let u62 := powTwoPow u31 31 * u31
    let u63 := powTwoPow u62 1 * u1
    u63 * u63

/-- The exponent identity behind one Itoh-Tsujii step. -/
private theorem chain_exponent (n m : ℕ) :
    (2 ^ n - 1) * 2 ^ m + (2 ^ m - 1) = 2 ^ (n + m) - 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [pow_add]
  generalize 2 ^ n = A at *
  generalize 2 ^ m = B at *
  cases A with
  | zero => omega
  | succ a =>
    cases B with
    | zero => omega
    | succ b => simp [Nat.succ_mul, Nat.mul_succ]

/-- The target of chain step `k`: `a ^ (2 ^ k - 1)`. -/
private noncomputable def chainTarget (q : AdjoinRoot basePoly) (k : ℕ) :
    AdjoinRoot basePoly := q ^ (2 ^ k - 1)

/-- The Itoh-Tsujii step: combining the `n`- and `m`-targets gives the `n + m`-target. -/
private theorem chainTarget_step {q x y : AdjoinRoot basePoly} {n m : ℕ}
    (hx : x = chainTarget q n) (hy : y = chainTarget q m) :
    x ^ (2 ^ m) * y = chainTarget q (n + m) := by
  rw [hx, hy, chainTarget, chainTarget, chainTarget, ← pow_mul, ← pow_add, chain_exponent]

/-- The Itoh-Tsujii chain computes `a ^ (2 ^ 64 - 2)`. -/
theorem toQuot_invItohTsujii (a : Base) (h : a ≠ 0) :
    toQuot (invItohTsujii a) = toQuot a ^ (2 ^ 64 - 2) := by
  rw [invItohTsujii, if_neg h]
  set q := toQuot a with hq
  have e1 : toQuot a = chainTarget q 1 := by
    simp only [chainTarget, hq]; norm_num
  have e2 : toQuot (powTwoPow a 1 * a) = chainTarget q 2 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e1 e1
  have e3 : toQuot (powTwoPow (powTwoPow a 1 * a) 1 * a) = chainTarget q 3 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e2 e1
  set u3 := powTwoPow (powTwoPow a 1 * a) 1 * a with hu3
  have e6 : toQuot (powTwoPow u3 3 * u3) = chainTarget q 6 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e3 e3
  set u6 := powTwoPow u3 3 * u3 with hu6
  have e7 : toQuot (powTwoPow u6 1 * a) = chainTarget q 7 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e6 e1
  set u7 := powTwoPow u6 1 * a with hu7
  have e14 : toQuot (powTwoPow u7 7 * u7) = chainTarget q 14 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e7 e7
  set u14 := powTwoPow u7 7 * u7 with hu14
  have e15 : toQuot (powTwoPow u14 1 * a) = chainTarget q 15 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e14 e1
  set u15 := powTwoPow u14 1 * a with hu15
  have e30 : toQuot (powTwoPow u15 15 * u15) = chainTarget q 30 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e15 e15
  set u30 := powTwoPow u15 15 * u15 with hu30
  have e31 : toQuot (powTwoPow u30 1 * a) = chainTarget q 31 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e30 e1
  set u31 := powTwoPow u30 1 * a with hu31
  have e62 : toQuot (powTwoPow u31 31 * u31) = chainTarget q 62 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e31 e31
  set u62 := powTwoPow u31 31 * u31 with hu62
  have e63 : toQuot (powTwoPow u62 1 * a) = chainTarget q 63 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e62 e1
  set u63 := powTwoPow u62 1 * a with hu63
  rw [toQuot_mul, e63, chainTarget, ← pow_add]
  congr 1

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

/-- The Itoh-Tsujii inverse really is a multiplicative inverse. -/
theorem mul_invItohTsujii {a : Base} (h : a ≠ 0) : a * invItohTsujii a = 1 := by
  have hq : toQuot a ≠ 0 := fun hz => h (toQuot_eq_zero_iff.mp hz)
  refine toQuot_injective ?_
  rw [toQuot_mul, toQuot_invItohTsujii a h, toQuot_one, ← pow_succ']
  have hcard : toQuot a ^ (2 ^ 64 - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (toQuot a) hq
    rwa [card_K] at this
  rw [show 2 ^ 64 - 2 + 1 = 2 ^ 64 - 1 from by norm_num]
  exact hcard

/-- Every nonzero carrier value has a multiplicative inverse. -/
theorem exists_mul_inv {a : Base} (h : a ≠ 0) : ∃ b : Base, a * b = 1 :=
  ⟨invItohTsujii a, mul_invItohTsujii h⟩

/-- Inversion is the Itoh-Tsujii chain, so it evaluates. -/
instance : Inv Base := ⟨invItohTsujii⟩

instance : Div Base := ⟨fun a b => a * invItohTsujii b⟩

theorem inv_def (a : Base) : a⁻¹ = invItohTsujii a := rfl

theorem div_def (a b : Base) : a / b = a * invItohTsujii b := rfl

@[simp] theorem inv_zero_base : (0 : Base)⁻¹ = 0 := by
  rw [inv_def, invItohTsujii, if_pos rfl]

theorem isField_base : IsField Base where
  exists_pair_ne := exists_pair_ne
  mul_comm := mul_comm
  mul_inv_cancel := fun h => exists_mul_inv h

/-- The carrier is a field: `K = GF(2^64)`.

Assembled field-by-field around the explicit Itoh-Tsujii inverse, so inversion and division
evaluate rather than being extracted from an existence proof. -/
instance : Field Base where
  inv := invItohTsujii
  div a b := a * invItohTsujii b
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := exists_pair_ne
  mul_inv_cancel _ h := mul_invItohTsujii h
  inv_zero := inv_zero_base
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

/-- The base field has characteristic two, inherited through the bridge. -/
instance : CharP Base 2 where
  cast_eq_zero_iff n := by
    rw [← toQuot_eq_zero_iff, toQuot_natCast]
    exact (CharP.cast_eq_zero_iff (AdjoinRoot basePoly) 2 n)

end Base

end
end LeanerVM.Parameters.Field
