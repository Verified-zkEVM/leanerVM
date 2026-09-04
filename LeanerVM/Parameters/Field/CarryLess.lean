/-
  LeanerVM.Parameters.Field.CarryLess

  Width-generic carry-less multiplication over `GF(2)`, and its agreement with
  polynomial multiplication.
-/

module

public import CompPoly.Fields.Binary.Common

/-!
# Width-generic carry-less multiplication

`CompPoly.Fields.Binary.Common` supplies the `BitVec`-to-polynomial bridge
`BinaryField.toPoly` generically in the bit width, but fixes its carry-less product
`BinaryField.clMul` at the 128-bit width used by `BF128Ghash`. The leanVM base field is
64-bit, so this module restates the product and its correctness generically.

Nothing here is leanVM-specific: it is general `GF(2)` polynomial arithmetic, and is a
candidate for upstreaming into CompPoly alongside the existing binary-field material.

## Main definitions and statements

* `zeroExtendTo` — widen a bit vector, and `toPoly_zeroExtendTo`, that widening preserves
  the polynomial denoted.
* `carryLessMul` — the carry-less product at an arbitrary result width.
* `toPoly_carryLessMul` — it denotes the product of the denoted polynomials, provided the
  result width admits the full product.
-/

namespace LeanerVM.Parameters.Field

open Polynomial BinaryField

public section

/-- Widen a bit vector by zero-extension. -/
def zeroExtendTo {v w : ℕ} (a : BitVec v) : BitVec w := BitVec.zeroExtend w a

theorem toNat_zeroExtendTo {v w : ℕ} (a : BitVec v) (h : v ≤ w) :
    (zeroExtendTo (w := w) a).toNat = a.toNat := by
  unfold zeroExtendTo
  simp [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by norm_num) h))

/-- Widening does not change the polynomial denoted. -/
theorem toPoly_zeroExtendTo {v w : ℕ} (a : BitVec v) (h : v ≤ w) :
    toPoly (zeroExtendTo (w := w) a) = toPoly a := by
  unfold toPoly BitVec.getLsb
  rw [toNat_zeroExtendTo a h]
  rw [Fin.sum_univ_eq_sum_range
        (f := fun i => if a.toNat.testBit i then (X : (ZMod 2)[X]) ^ i else 0),
      Fin.sum_univ_eq_sum_range
        (f := fun i => if a.toNat.testBit i then (X : (ZMod 2)[X]) ^ i else 0)]
  refine (Finset.sum_subset (s₁ := Finset.range v) (s₂ := Finset.range w)
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)) ?_).symm
  intro i _ hnot
  simp only [Finset.mem_range, not_lt] at hnot
  have hlt : a.toNat < 2 ^ i :=
    lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by norm_num) hnot)
  simp [Nat.testBit_lt_two_pow hlt]

/-- The carry-less (polynomial) product, at an arbitrary result width. -/
def carryLessMul {v w : ℕ} (a b : BitVec v) : BitVec w :=
  Fin.foldl v (fun acc i => if a.getLsbD i then acc ^^^ (zeroExtendTo b <<< (i : Nat)) else acc) 0

private theorem carryLessMul_unfold {v w : ℕ} (a b : BitVec v) :
    carryLessMul (w := w) a b = Fin.foldl v
      (fun acc i =>
        acc ^^^ (if a.getLsbD i then (zeroExtendTo b : BitVec w) <<< (i : Nat) else 0)) 0 := by
  unfold carryLessMul
  congr
  funext acc i
  cases h : BitVec.getLsbD a i <;> simp

/-- `carryLessMul` denotes the product of the denoted polynomials, provided the result
width admits the full product. -/
theorem toPoly_carryLessMul {v w : ℕ} (a b : BitVec v) (h : v + v ≤ w) :
    toPoly (carryLessMul (w := w) a b) = toPoly a * toPoly b := by
  rw [carryLessMul_unfold]
  rw [toPoly_fold_xor
    (f := fun k => if a.getLsbD k = true then (zeroExtendTo b : BitVec w) <<< k else 0)]
  conv_rhs => enter [1]; unfold toPoly
  unfold BitVec.getLsb
  rw [Fin.sum_univ_eq_sum_range
    (f := fun i => if (BitVec.toNat a).testBit i = true then X ^ i else 0)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  unfold BitVec.getLsbD
  split_ifs
  · have hb : (zeroExtendTo b : BitVec w).toNat < 2 ^ v := by
      rw [toNat_zeroExtendTo b (by omega)]; exact b.isLt
    rw [toPoly_shiftLeft_no_overflow (d := v) (zeroExtendTo b) (ha := hb)
        (h_no_overflow := by omega)]
    rw [toPoly_zeroExtendTo b (by omega)]
    ring
  · simp [toPoly_zero_eq_zero]

end
end LeanerVM.Parameters.Field
