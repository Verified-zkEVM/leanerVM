/-
  LeanerVM.Parameters.ToCompPoly.BF64Fast

  `GF(2^64)` arithmetic on machine words for CompPoly's `BF64`: carry-less multiplication by
  integer multiplication of sparse words, the reduction, the inverse and powers, with the
  instances on words registered for compilation. Candidate for CompPoly.
-/

module

public import CompPoly.Fields.Binary.BF64.Impl
import Mathlib.Algebra.Ring.Ext
import Mathlib.Tactic.LinearCombination

/-!
# Fast `GF(2^64)` on words

CompPoly's `BF64.mul` is the specification: a 64-step loop that builds the carry-less product
in a `BitVec 128`, then two folds. This module computes the same product on `UInt64`, and
registers the result for compiled code with `@[csimp]` theorems, which the kernel checks and the
compiler uses to substitute one constant for another. Types, definitions and every theorem about
`BF64` are unchanged; only compiled code differs.

**What is substituted.** A call site `a * b` reaches `BF64.mul` only through the instance
`BF64.instMul`, whose compiled body was fixed when CompPoly was compiled, so a `@[csimp]` theorem
on `BF64.mul` itself never fires. The theorems here replace the *instance constants*:
`BF64.instMul`, `BF64.instPowNat`, `BF64.instInv`, `BF64.instDiv`, `BF64.instCommRing` and
`BF64.instField`, each by a structure whose operations run on words. Every compiled call site
that names one of them, directly or as the dictionary passed to generic code (`Finset.sum`,
`npowBinRec`, CompPoly's extension fields and multilinear evaluation), uses the word operations.

**The product.** `clmul32` multiplies the low 32 bits of two words carry-lessly with sixteen
integer multiplications: masked to every fourth bit, the words' bits are base-16 digits that are
`0` or `1`, so a product's digits count at most eight pairs and never carry; the parity of a
digit is the carry-less coefficient (the idea of BearSSL's `bmul`, `src/hash/ghash_ctmul64.c`).
`clmul64` is three such products of halves (Karatsuba) and `reduceWords` folds the high word by
`X^64 = X^4 + X^3 + X + 1` twice. `mulFast` short-cuts the products by `0` and `1`. The field
structure `fieldFast` also takes integer powers on words (`zpowFast`); its rational casts and
scalar products stay those of `BF64.instField`.

## Main statements

* `toPoly_clmul32`, `toPoly_clmul64`, `toPoly_reduceWords` — the word operations denote the
  polynomial product and the remainder modulo `BF64.basePoly`.
* `mulFast_eq`, `invFast_eq`, `powFast_eq` — the word operations agree with `BF64`'s.
* the `@[csimp]` theorems `instMul_eq_instMulFast` through `instField_eq_fieldFast`.

## Upstream

CompPoly would carry `clmul32` through `invWord` with their proofs, and attach the substitution
to its own definitions: a `@[csimp]` theorem `BF64.mul = …` in the module that defines `BF64.mul`
fires for the instances compiled after it, which makes the instance-level theorems here
unnecessary. Storing a `BF64` as a `UInt64` would remove the conversions as well.

## Implementation notes

A `BF64` stores a `BitVec 64`, a natural number at run time, so the conversions to and from a
word stay: an element with its top bit set is a heap-allocated big integer.
-/

namespace LeanerVM.Parameters.FastBF64

open Polynomial BinaryField BF64

@[expose] public section

/-- Bit `4k + b` of a polynomial with coefficients below 16, evaluated at 16, is bit `b` of
coefficient `k`. -/
private theorem testBit_eval_sixteen (Q : ℕ[X]) (hQ : ∀ i, Q.coeff i < 16) (k b : ℕ) (hb : b < 4) :
    (Q.eval 16).testBit (4 * k + b) = (Q.coeff k).testBit b := by
  induction k generalizing Q <;>
    rw [show Q.eval 16 = 2 ^ 4 * (divX Q).eval 16 + Q.coeff 0 by
      conv_lhs => rw [← divX_mul_X_add Q]
      rw [eval_add, eval_mul_X, eval_C]; ring, Nat.testBit_two_pow_mul_add (i := 4) _ (hQ 0)]
  case zero => simp [hb]
  case succ k ih =>
    simp only [show ¬ 4 * (k + 1) + b < 4 by omega, ↓reduceIte,
      show 4 * (k + 1) + b - 4 = 4 * k + b by omega]
    rw [ih _ fun i ↦ coeff_divX (p := Q) ▸ hQ _, coeff_divX]

/-- Bit `p` of `2^r` times a digit polynomial at 16. -/
private theorem testBit_two_pow_mul_eval (Q : ℕ[X]) (hQ : ∀ i, Q.coeff i < 16) (r p : ℕ) :
    (2 ^ r * Q.eval 16).testBit p =
      (decide (r ≤ p) && (Q.coeff ((p - r) / 4)).testBit ((p - r) % 4)) := by
  rw [Nat.testBit_two_pow_mul, ← testBit_eval_sixteen Q hQ _ _ (Nat.mod_lt _ (by norm_num)),
    Nat.div_add_mod]

/-- The digit polynomial of residue `r`: coefficient `i` is bit `4i + r` of `x`, for `i < 8`. -/
private noncomputable def dig (x r : ℕ) : ℕ[X] :=
  ∑ i ∈ Finset.range 8, C (x.testBit (4 * i + r)).toNat * X ^ i

private theorem coeff_dig (x r k : ℕ) :
    (dig x r).coeff k = if k < 8 then (x.testBit (4 * k + r)).toNat else 0 := by
  simp [dig, finsetSum_coeff]

private theorem coeff_dig_le (x r k : ℕ) : (dig x r).coeff k ≤ 1 := by
  rw [coeff_dig]; split_ifs <;> simp [Bool.toNat_le]

/-- A product of two digit polynomials has coefficients at most 8, below 16. -/
private theorem coeff_dig_mul_lt (x y r s k : ℕ) : (dig x r * dig y s).coeff k < 16 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc _ ≤ ∑ i ∈ Finset.range k.succ, if i < 8 then 1 else 0 :=
        Finset.sum_le_sum fun i _ ↦ by
          rw [coeff_dig x r i]
          split_ifs
          · exact Nat.mul_le_mul (Bool.toNat_le _) (coeff_dig_le y s _)
          · simp
    _ = ((Finset.range k.succ).filter (· < 8)).card := by rw [Finset.sum_boole]; simp
    _ ≤ (Finset.range 8).card := Finset.card_le_card fun i ↦ by simp
    _ < 16 := by simp

/-- The all-ones digit polynomial with `n` digits. -/
private noncomputable def onesN (n : ℕ) : ℕ[X] := ∑ i ∈ Finset.range n, X ^ i

private theorem coeff_onesN (n k : ℕ) : (onesN n).coeff k = if k < n then 1 else 0 := by
  simp [onesN, finsetSum_coeff]

/-- Bit `p` of `2^r` times the mask with `n` digits `1`. -/
private theorem testBit_mask (n r p : ℕ) :
    (2 ^ r * (onesN n).eval 16).testBit p =
      decide (r ≤ p ∧ (p - r) / 4 < n ∧ (p - r) % 4 = 0) := by
  rw [testBit_two_pow_mul_eval _ (fun i ↦ by rw [coeff_onesN]; split_ifs <;> norm_num),
    coeff_onesN]
  split_ifs <;> simp [*, ← Bool.toNat_true, Nat.testBit_bool_toNat]

/-- Masking with every fourth bit from `r` keeps the digits of residue `r`. -/
private theorem and_mask (x r : ℕ) :
    x &&& (2 ^ r * 0x11111111) = 2 ^ r * (dig x r).eval 16 := by
  apply Nat.eq_of_testBit_eq fun p ↦ ?_
  rw [Nat.testBit_and,
    show (0x11111111 : ℕ) = (onesN 8).eval 16 by simp [onesN, Finset.sum_range_succ], testBit_mask,
    testBit_two_pow_mul_eval _ fun i ↦ (coeff_dig_le x r i).trans_lt (by norm_num), coeff_dig]
  by_cases h : r ≤ p ∧ (p - r) / 4 < 8 ∧ (p - r) % 4 = 0
  · simp [h, show 4 * ((p - r) / 4) + r = p by omega]
    cases x.testBit p <;> rfl
  · rw [decide_eq_false h, Bool.and_false]
    split_ifs <;> simp only [Nat.testBit_bool_toNat, Nat.zero_testBit, Bool.and_false]
    by_cases h1 : r ≤ p <;> simp_all

/-- Bit `4k + t` of a product of two masked words, `r + s = t + 4v`: the parity of coefficient
`k` of the digit product shifted by `v`. -/
private theorem testBit_and_mask_mul (x y r s t v k : ℕ) (h : r + s = t + 4 * v) :
    ((x &&& (2 ^ r * 0x11111111)) * (y &&& (2 ^ s * 0x11111111))).testBit (4 * k + t) =
      ((X ^ v * (dig x r * dig y s)).coeff k).bodd := by
  rw [and_mask, and_mask, show 2 ^ r * eval 16 (dig x r) * (2 ^ s * eval 16 (dig y s)) =
      2 ^ t * (X ^ v * (dig x r * dig y s)).eval 16 by
    rw [eval_mul, eval_mul, eval_pow, eval_X, show (16 : ℕ) ^ v = 2 ^ (4 * v) by rw [pow_mul]; rfl]
    calc _ = 2 ^ (r + s) * (eval 16 (dig x r) * eval 16 (dig y s)) := by ring
      _ = _ := by rw [h]; ring,
    testBit_two_pow_mul_eval _ fun i ↦ by
      rw [coeff_X_pow_mul']; split_ifs <;> simp [coeff_dig_mul_lt]]
  simp [Nat.bodd]

/-- Coefficient `4k + t` of `X^c` times a polynomial in `X^4`. -/
private theorem coeff_X_pow_mul_expand {R : Type*} [CommSemiring R] (Q : R[X]) (c k t : ℕ)
    (ht : t < 4) :
    (X ^ c * expand R 4 Q).coeff (4 * k + t) =
      if c % 4 = t then (X ^ (c / 4) * Q).coeff k else 0 := by
  rw [coeff_X_pow_mul', coeff_X_pow_mul', coeff_expand (by norm_num)]
  split_ifs <;> first | omega | (congr 1; omega) | rfl

/-- The bits of `x` below 32 as a polynomial, gathered by residue modulo 4. -/
private noncomputable def bitPoly (x : ℕ) : ℕ[X] :=
  ∑ r ∈ Finset.range 4, X ^ r * expand ℕ 4 (dig x r)

private theorem coeff_bitPoly (x i : ℕ) :
    (bitPoly x).coeff i = if i < 32 then (x.testBit i).toNat else 0 := by
  obtain ⟨k, t, ht, rfl⟩ : ∃ k t, t < 4 ∧ i = 4 * k + t := ⟨i / 4, i % 4, by omega, by omega⟩
  simp only [bitPoly, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, coeff_add,
    coeff_X_pow_mul_expand _ _ _ _ ht]
  simp only [Nat.reduceMod, Nat.reduceDiv, pow_zero, one_mul, coeff_dig,
    show 4 * k + t < 32 ↔ k < 8 by omega]
  obtain rfl | rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := (by omega) <;> simp

/-- Carry-less product of the low 32 bits of two words, by integer multiplication of the words
masked to every fourth bit: the four residues never carry into each other. -/
@[inline] def clmul32 (x y : UInt64) : UInt64 :=
  let x0 := x &&& 0x11111111
  let x1 := x &&& 0x22222222
  let x2 := x &&& 0x44444444
  let x3 := x &&& 0x88888888
  let y0 := y &&& 0x11111111
  let y1 := y &&& 0x22222222
  let y2 := y &&& 0x44444444
  let y3 := y &&& 0x88888888
  let z0 := (x0 * y0) ^^^ (x1 * y3) ^^^ (x2 * y2) ^^^ (x3 * y1)
  let z1 := (x0 * y1) ^^^ (x1 * y0) ^^^ (x2 * y3) ^^^ (x3 * y2)
  let z2 := (x0 * y2) ^^^ (x1 * y1) ^^^ (x2 * y0) ^^^ (x3 * y3)
  let z3 := (x0 * y3) ^^^ (x1 * y2) ^^^ (x2 * y1) ^^^ (x3 * y0)
  (z0 &&& 0x1111111111111111) ||| (z1 &&& 0x2222222222222222) |||
    (z2 &&& 0x4444444444444444) ||| (z3 &&& 0x8888888888888888)

/-- A product of two words masked below `2^32` does not wrap. -/
private theorem toNat_and_mul_and (x y m n : UInt64) (hm : m.toNat < 2 ^ 32)
    (hn : n.toNat < 2 ^ 32) :
    ((x &&& m) * (y &&& n)).toNat = (x.toNat &&& m.toNat) * (y.toNat &&& n.toNat) := by
  rw [UInt64.toNat_mul, UInt64.toNat_and, UInt64.toNat_and, Nat.mod_eq_of_lt]
  exact (Nat.mul_lt_mul'' (Nat.and_lt_two_pow _ hm) (Nat.and_lt_two_pow _ hn)).trans_eq rfl

/-- `clmul32` on natural numbers. -/
private theorem toNat_clmul32 (x y : UInt64) : (clmul32 x y).toNat =
    let X := x.toNat; let Y := y.toNat
    let x0 := X &&& (2 ^ 0 * 0x11111111); let x1 := X &&& (2 ^ 1 * 0x11111111)
    let x2 := X &&& (2 ^ 2 * 0x11111111); let x3 := X &&& (2 ^ 3 * 0x11111111)
    let y0 := Y &&& (2 ^ 0 * 0x11111111); let y1 := Y &&& (2 ^ 1 * 0x11111111)
    let y2 := Y &&& (2 ^ 2 * 0x11111111); let y3 := Y &&& (2 ^ 3 * 0x11111111)
    ((x0 * y0 ^^^ x1 * y3 ^^^ x2 * y2 ^^^ x3 * y1) &&& (2 ^ 0 * (onesN 16).eval 16)) |||
    ((x0 * y1 ^^^ x1 * y0 ^^^ x2 * y3 ^^^ x3 * y2) &&& (2 ^ 1 * (onesN 16).eval 16)) |||
    ((x0 * y2 ^^^ x1 * y1 ^^^ x2 * y0 ^^^ x3 * y3) &&& (2 ^ 2 * (onesN 16).eval 16)) |||
    ((x0 * y3 ^^^ x1 * y2 ^^^ x2 * y1 ^^^ x3 * y0) &&& (2 ^ 3 * (onesN 16).eval 16)) := by
  have he : (onesN 16).eval 16 = 0x1111111111111111 := by simp [onesN, Finset.sum_range_succ]
  simp (disch := decide) only [clmul32, UInt64.toNat_or, UInt64.toNat_and, UInt64.toNat_xor,
    toNat_and_mul_and, he]
  rfl

/-- The coefficients of the product of two bit polynomials, by residue. -/
private theorem coeff_bitPoly_mul (x y k t : ℕ) (ht : t < 4) :
    (bitPoly x * bitPoly y).coeff (4 * k + t) =
      ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4,
        if (r + s) % 4 = t then (X ^ ((r + s) / 4) * (dig x r * dig y s)).coeff k else 0 := by
  simp only [bitPoly, Finset.sum_mul_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [show X ^ r * expand ℕ 4 (dig x r) * (X ^ s * expand ℕ 4 (dig y s)) =
    X ^ (r + s) * expand ℕ 4 (dig x r * dig y s) by rw [map_mul, pow_add]; ring]
  exact coeff_X_pow_mul_expand _ _ _ _ ht

private theorem mask_select (t' t k : ℕ) (ht' : t' < 4) (ht : t < 4) (hk : 4 * k + t < 64) :
    decide (t' ≤ 4 * k + t ∧ (4 * k + t - t') / 4 < 16 ∧ (4 * k + t - t') % 4 = 0) =
      decide (t' = t) := by
  rw [decide_eq_decide]; omega

/-- Bit `p` of `clmul32 x y` is the parity of coefficient `p` of the product of the low 32 bits of
`x` and `y` as polynomials. -/
private theorem testBit_clmul32 (x y : UInt64) (p : ℕ) (hp : p < 64) :
    (clmul32 x y).toNat.testBit p = ((bitPoly x.toNat * bitPoly y.toNat).coeff p).bodd := by
  obtain ⟨k, t, ht, rfl⟩ : ∃ k t, t < 4 ∧ p = 4 * k + t := ⟨p / 4, p % 4, by omega, by omega⟩
  rw [toNat_clmul32, coeff_bitPoly_mul _ _ _ _ ht]
  simp only [Nat.testBit_or, Nat.testBit_and, testBit_mask, Nat.testBit_xor,
    mask_select _ t k (by norm_num : 0 < 4) ht hp, mask_select _ t k (by norm_num : 1 < 4) ht hp,
    mask_select _ t k (by norm_num : 2 < 4) ht hp, mask_select _ t k (by norm_num : 3 < 4) ht hp]
  obtain rfl | rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := (by omega)
  all_goals simp only [
    testBit_and_mask_mul _ _ 0 0 _ 0 k rfl, testBit_and_mask_mul _ _ 1 3 _ 1 k rfl,
    testBit_and_mask_mul _ _ 2 2 _ 1 k rfl, testBit_and_mask_mul _ _ 3 1 _ 1 k rfl,
    testBit_and_mask_mul _ _ 0 1 _ 0 k rfl, testBit_and_mask_mul _ _ 1 0 _ 0 k rfl,
    testBit_and_mask_mul _ _ 2 3 _ 1 k rfl, testBit_and_mask_mul _ _ 3 2 _ 1 k rfl,
    testBit_and_mask_mul _ _ 0 2 _ 0 k rfl, testBit_and_mask_mul _ _ 1 1 _ 0 k rfl,
    testBit_and_mask_mul _ _ 2 0 _ 0 k rfl, testBit_and_mask_mul _ _ 3 3 _ 1 k rfl,
    testBit_and_mask_mul _ _ 0 3 _ 0 k rfl, testBit_and_mask_mul _ _ 1 2 _ 0 k rfl,
    testBit_and_mask_mul _ _ 2 1 _ 0 k rfl, testBit_and_mask_mul _ _ 3 0 _ 0 k rfl]
  all_goals simp only [Nat.reduceEqDiff, decide_true, decide_false, Bool.and_true, Bool.and_false,
    Bool.or_false, Bool.false_or, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero,
    Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, ↓reduceIte, Nat.bodd_add]

private theorem coeff_bitPoly_mul_eq_zero (x y p : ℕ) (hp : 64 ≤ p) :
    (bitPoly x * bitPoly y).coeff p = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij ↦ ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [coeff_bitPoly, coeff_bitPoly]
  split_ifs <;> omega

/-- A word below `2^32` denotes its bit polynomial. -/
private theorem toPoly_eq_map_bitPoly (v : BitVec 64) (hv : v.toNat < 2 ^ 32) :
    toPoly v = (bitPoly v.toNat).map (Nat.castRingHom (ZMod 2)) := by
  ext i
  have h := fun h : 32 ≤ i ↦
    Nat.testBit_lt_two_pow (hv.trans_le (Nat.pow_le_pow_right (by norm_num) h))
  rw [toPoly_coeff, coeff_map, coeff_bitPoly]
  split_ifs <;> cases hb : v.toNat.testBit i <;> simp_all [BitVec.getLsb]
  omega

private theorem bitPoly_and_low (x : ℕ) : bitPoly (x &&& 0xFFFFFFFF) = bitPoly x := by
  ext i
  simp only [coeff_bitPoly, Nat.testBit_and, show (0xFFFFFFFF : ℕ) = 2 ^ 32 - 1 from rfl,
    Nat.testBit_two_pow_sub_one]
  grind

/-- `clmul32` is the carry-less product of the low halves. -/
theorem toPoly_clmul32 (x y : UInt64) :
    toPoly (clmul32 x y).toBitVec =
      toPoly (x &&& 0xFFFFFFFF).toBitVec * toPoly (y &&& 0xFFFFFFFF).toBitVec := by
  have hlow : ∀ z : UInt64, (z &&& 0xFFFFFFFF).toBitVec.toNat < 2 ^ 32 := fun z ↦ by
    rw [UInt64.toNat_toBitVec, UInt64.toNat_and]
    exact Nat.and_lt_two_pow _ (by decide)
  rw [toPoly_eq_map_bitPoly _ (hlow x), toPoly_eq_map_bitPoly _ (hlow y), ← Polynomial.map_mul]
  simp only [UInt64.toNat_toBitVec, UInt64.toNat_and,
    show UInt64.toNat 4294967295 = 0xFFFFFFFF from rfl, bitPoly_and_low]
  ext p
  rw [toPoly_coeff, coeff_map]
  by_cases hp : p < 64
  · simp only [hp, ↓reduceDIte, BitVec.getLsb, UInt64.toNat_toBitVec, testBit_clmul32 x y p hp,
      Nat.coe_castRingHom]
    rw [← ZMod.natCast_mod, Nat.mod_two_of_bodd]
    cases Nat.bodd _ <;> rfl
  · simp [hp, coeff_bitPoly_mul_eq_zero _ _ _ (not_lt.mp hp)]


/-! ## Words and their polynomials -/

private theorem testBit_word_ge (a : UInt64) (j : ℕ) (hj : 64 ≤ j) : a.toNat.testBit j = false :=
  Nat.testBit_lt_two_pow (a.toNat_lt.trans_le (Nat.pow_le_pow_right (by norm_num) hj))

/-- Coefficient `n` of a word's polynomial is its bit `n`. -/
private theorem coeff_toPoly_word (a : UInt64) (n : ℕ) :
    (toPoly a.toBitVec).coeff n = if a.toNat.testBit n then 1 else 0 := by
  rw [toPoly_coeff]
  by_cases hn : n < 64
  · simp [hn, BitVec.getLsb]
  · simp [hn, testBit_word_ge a n (by omega)]

private theorem testBit_shiftRight_word (a s : UInt64) (hs : s.toNat < 64) (j : ℕ) :
    (a >>> s).toNat.testBit j = a.toNat.testBit (j + s.toNat) := by
  rw [UInt64.toNat_shiftRight, Nat.testBit_shiftRight, Nat.mod_eq_of_lt hs, Nat.add_comm]

private theorem testBit_shiftLeft_word (a s : UInt64) (hs : s.toNat < 64) (j : ℕ) :
    (a <<< s).toNat.testBit j =
      (decide (s.toNat ≤ j) && decide (j < 64) && a.toNat.testBit (j - s.toNat)) := by
  rw [UInt64.toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.mod_eq_of_lt hs]
  cases decide (s.toNat ≤ j) <;> cases decide (j < 64) <;> simp [Bool.and_comm]

private theorem testBit_and_low32 (a : UInt64) (j : ℕ) :
    (a &&& 0xFFFFFFFF).toNat.testBit j = (decide (j < 32) && a.toNat.testBit j) := by
  rw [UInt64.toNat_and, Nat.testBit_and, show UInt64.toNat 0xFFFFFFFF = 2 ^ 32 - 1 from rfl,
    Nat.testBit_two_pow_sub_one, Bool.and_comm]

/-- A word shifted left by `k` and right by `64 - k`: the two parts of `m * X^k`. -/
private theorem toPoly_shift_pair (m s s' : UInt64) (hk : 0 < s.toNat) (hs : s.toNat < 64)
    (hs' : s'.toNat = 64 - s.toNat) :
    toPoly (m >>> s').toBitVec * X ^ 64 + toPoly (m <<< s).toBitVec =
      toPoly m.toBitVec * X ^ s.toNat := by
  ext n
  rw [coeff_add, coeff_mul_X_pow', coeff_mul_X_pow', coeff_toPoly_word, coeff_toPoly_word,
    coeff_toPoly_word, testBit_shiftRight_word _ _ (by omega), testBit_shiftLeft_word _ _ hs, hs']
  by_cases h64 : 64 ≤ n
  · simp [h64, show n - 64 + (64 - s.toNat) = n - s.toNat by omega, show ¬ n < 64 by omega,
      show s.toNat ≤ n by omega]
  · by_cases hsn : s.toNat ≤ n <;> simp [h64, hsn, show n < 64 by omega]

/-- A word is its high half times `X^32` plus its low half. -/
private theorem toPoly_word_split (a : UInt64) :
    toPoly a.toBitVec =
      toPoly (a >>> 32).toBitVec * X ^ 32 + toPoly (a &&& 0xFFFFFFFF).toBitVec := by
  ext n
  rw [coeff_add, coeff_mul_X_pow', coeff_toPoly_word, coeff_toPoly_word, coeff_toPoly_word,
    testBit_and_low32, testBit_shiftRight_word _ _ (by decide)]
  by_cases h32 : 32 ≤ n
  · simp [h32, show n - 32 + 32 = n by omega, show ¬ n < 32 by omega]
  · simp [h32, show n < 32 by omega]

private theorem toPoly_xor_high_low (a : UInt64) :
    toPoly ((a ^^^ (a >>> 32)) &&& 0xFFFFFFFF).toBitVec =
      toPoly (a &&& 0xFFFFFFFF).toBitVec + toPoly (a >>> 32).toBitVec := by
  ext n
  rw [coeff_add, coeff_toPoly_word, coeff_toPoly_word, coeff_toPoly_word, testBit_and_low32,
    testBit_and_low32, UInt64.toNat_xor, Nat.testBit_xor, testBit_shiftRight_word _ _ (by decide)]
  by_cases hn : n < 32
  · simp only [hn, decide_true, Bool.true_and]
    cases a.toNat.testBit n <;> cases a.toNat.testBit (n + UInt64.toNat 32) <;> decide
  · simp [hn, testBit_word_ge a (n + 32) (by omega)]

private theorem toPoly_high_low (a : UInt64) :
    toPoly ((a >>> 32) &&& 0xFFFFFFFF).toBitVec = toPoly (a >>> 32).toBitVec := by
  ext n
  rw [coeff_toPoly_word, coeff_toPoly_word, testBit_and_low32,
    testBit_shiftRight_word _ _ (by decide)]
  by_cases hn : n < 32
  · simp [hn]
  · simp [hn, testBit_word_ge a (n + 32) (by omega)]

/-- The carry-less product of two words, as its high and low words: three products of halves
(Karatsuba). -/
@[inline] def clmul64 (a b : UInt64) : UInt64 × UInt64 :=
  let a1 := a >>> 32
  let b1 := b >>> 32
  let p := clmul32 a b
  let q := clmul32 a1 b1
  let m := clmul32 (a ^^^ a1) (b ^^^ b1) ^^^ p ^^^ q
  (q ^^^ (m >>> 32), p ^^^ (m <<< 32))

/-- `clmul64` is the carry-less product, as a high and a low word. -/
theorem toPoly_clmul64 (a b : UInt64) :
    toPoly (clmul64 a b).1.toBitVec * X ^ 64 + toPoly (clmul64 a b).2.toBitVec =
      toPoly a.toBitVec * toPoly b.toBitVec := by
  simp only [clmul64, UInt64.toBitVec_xor, toPoly_xor]
  have hm := toPoly_shift_pair (clmul32 (a ^^^ a >>> 32) (b ^^^ b >>> 32) ^^^ clmul32 a b ^^^
    clmul32 (a >>> 32) (b >>> 32)) 32 32 (by decide) (by decide) (by decide)
  simp only [UInt64.toBitVec_xor, toPoly_xor, toPoly_clmul32, toPoly_xor_high_low,
    toPoly_high_low, show UInt64.toNat 32 = 32 from rfl] at hm ⊢
  rw [toPoly_word_split a, toPoly_word_split b]
  linear_combination hm + (toPoly (a &&& 0xFFFFFFFF).toBitVec * toPoly (b &&& 0xFFFFFFFF).toBitVec +
    toPoly (a >>> 32).toBitVec * toPoly (b >>> 32).toBitVec) * X ^ 32 * ZMod2Poly.two_eq_zero

/-- Reduce `hi · X^64 + lo` modulo `X^64 + X^4 + X^3 + X + 1`: `X^64 = X^4 + X^3 + X + 1` folds
`hi` down, and the at most four bits it pushes past `X^63` fold down once more. -/
@[inline] def reduceWords (hi lo : UInt64) : UInt64 :=
  let t := hi ^^^ (hi <<< 1) ^^^ (hi <<< 3) ^^^ (hi <<< 4)
  let o := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  lo ^^^ t ^^^ o ^^^ (o <<< 1) ^^^ (o <<< 3) ^^^ (o <<< 4)

private theorem shiftRight_eq_zero_of_lt (o s : UInt64) (ho : o.toNat < 16) (hs : 4 ≤ s.toNat)
    (hs' : s.toNat < 64) : toPoly (o >>> s).toBitVec = 0 := by
  rw [show o >>> s = 0 from UInt64.toNat_inj.mp <| by
    rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hs', Nat.shiftRight_eq_div_pow,
      UInt64.toNat_zero, Nat.div_eq_zero_iff_lt (by positivity)]
    exact ho.trans_le (Nat.pow_le_pow_right (n := 2) (by norm_num) hs)]
  exact toPoly_zero_eq_zero

/-- `reduceWords` computes the remainder modulo `BF64.basePoly`. -/
theorem toPoly_reduceWords (hi lo : UInt64) :
    toPoly (reduceWords hi lo).toBitVec =
      (toPoly hi.toBitVec * X ^ 64 + toPoly lo.toBitVec) % BF64.basePoly := by
  set o := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60) with ho
  have ho16 : o.toNat < 16 := by
    have h := hi.toNat_lt
    simp only [o, UInt64.toNat_xor, UInt64.toNat_shiftRight,
      show UInt64.toNat 63 % 64 = 63 from rfl, show UInt64.toNat 61 % 64 = 61 from rfl,
      show UInt64.toNat 60 % 64 = 60 from rfl, Nat.shiftRight_eq_div_pow]
    refine Nat.xor_lt_two_pow (n := 4) (Nat.xor_lt_two_pow ?_ ?_) ?_ <;>
      exact Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact h.trans_le (Nat.pow_le_pow_right
        (by norm_num) (by norm_num)))
  have p1 := toPoly_shift_pair hi 1 63 (by decide) (by decide) (by decide)
  have p3 := toPoly_shift_pair hi 3 61 (by decide) (by decide) (by decide)
  have p4 := toPoly_shift_pair hi 4 60 (by decide) (by decide) (by decide)
  have q1 := toPoly_shift_pair o 1 63 (by decide) (by decide) (by decide)
  have q3 := toPoly_shift_pair o 3 61 (by decide) (by decide) (by decide)
  have q4 := toPoly_shift_pair o 4 60 (by decide) (by decide) (by decide)
  simp only [shiftRight_eq_zero_of_lt o 63 ho16 (by decide) (by decide),
    shiftRight_eq_zero_of_lt o 61 ho16 (by decide) (by decide),
    shiftRight_eq_zero_of_lt o 60 ho16 (by decide) (by decide), zero_mul, zero_add,
    show UInt64.toNat 1 = 1 from rfl, show UInt64.toNat 3 = 3 from rfl,
    show UInt64.toNat 4 = 4 from rfl] at p1 p3 p4 q1 q3 q4
  have hdeg : (toPoly (reduceWords hi lo).toBitVec).degree < BF64.basePoly.degree := by
    rw [BF64.basePoly_degree]; exact toPoly_degree_lt_w (by norm_num) _
  rw [← (Polynomial.mod_eq_self_iff BF64.basePoly_ne_zero).mpr hdeg]
  have hO : toPoly o.toBitVec =
      toPoly (hi >>> 63).toBitVec + toPoly (hi >>> 61).toBitVec + toPoly (hi >>> 60).toBitVec := by
    simp only [o, UInt64.toBitVec_xor, toPoly_xor]
  refine (CanonicalEuclideanDomain.mod_eq_of_eq_add_mul
    (q := toPoly hi.toBitVec + toPoly o.toBitVec) ?_ BF64.basePoly_ne_zero).symm
  simp only [reduceWords, ← ho, UInt64.toBitVec_xor, toPoly_xor]
  rw [BF64.basePoly_eq]
  linear_combination (-1 : (ZMod 2)[X]) * p1 - p3 - p4 - q1 - q3 - q4 - X ^ 64 * hO -
    (toPoly hi.toBitVec + toPoly o.toBitVec) * (1 + X + X ^ 3 + X ^ 4) * ZMod2Poly.two_eq_zero

/-- The product of two words in `GF(2^64)`. -/
@[inline] def mulWord (a b : UInt64) : UInt64 :=
  let hl := clmul64 a b
  reduceWords hl.1 hl.2

/-- `mulWord` is the product modulo `BF64.basePoly`. -/
theorem toPoly_mulWord (a b : UInt64) :
    toPoly (mulWord a b).toBitVec = (toPoly a.toBitVec * toPoly b.toBitVec) % BF64.basePoly := by
  rw [mulWord, toPoly_reduceWords, toPoly_clmul64]

private theorem toPoly_injective64 {u v : BitVec 64} (h : toPoly u = toPoly v) : u = v := by
  have hx : toPoly (u ^^^ v) = 0 := by rw [toPoly_xor, h, ZMod2Poly.add_self_cancel]
  by_contra hne
  exact ((toPoly_ne_zero_iff_ne_zero (u ^^^ v)).mpr
    (fun h0 ↦ hne (BitVec.xor_eq_zero_iff.mp h0))) hx

/-- The word of an element. -/
@[inline] def toWord (a : BF64) : UInt64 := UInt64.ofBitVec a.toBitVec

/-- The element of a word. -/
@[inline] def ofWord (w : UInt64) : BF64 := BF64.ofBitVec w.toBitVec

/-- An element is the element of its word. -/
@[simp] theorem ofWord_toWord (a : BF64) : ofWord (toWord a) = a := rfl

/-- Distinct elements have distinct words. -/
theorem toWord_injective : Function.Injective toWord := fun a b h ↦ by
  rw [← ofWord_toWord a, h, ofWord_toWord]

/-- `mulWord` is `BF64`'s multiplication. -/
theorem ofWord_mulWord (a b : UInt64) : ofWord (mulWord a b) = ofWord a * ofWord b := by
  apply BF64.ext
  rw [toBitVec_mul]
  apply toPoly_injective64
  rw [ofWord, ofWord, ofWord, toBitVec_ofBitVec, toBitVec_ofBitVec, toBitVec_ofBitVec,
    toPoly_mulWord, toPoly_reduce, toPoly_carryLessMul _ _ (by norm_num)]

/-- Multiplication on words, with the products by `0` and `1` short-cut. -/
def mulFast (a b : BF64) : BF64 :=
  let y := toWord b
  if y == 1 then a else if y == 0 then 0 else ofWord (mulWord (toWord a) y)

/-- `mulFast` is `BF64`'s multiplication. -/
theorem mulFast_eq (a b : BF64) : mulFast a b = a * b := by
  simp only [mulFast]
  split_ifs with h1 h0
  · have : b = 1 := toWord_injective (by rw [beq_iff_eq] at h1; exact h1)
    rw [this, mul_one]
  · have : b = 0 := toWord_injective (by rw [beq_iff_eq] at h0; exact h0)
    rw [this, mul_zero]
  · rw [ofWord_mulWord, ofWord_toWord, ofWord_toWord]

/-- `a ^ (2 ^ k)` on words, by `k` squarings. -/
def powTwoPowWord (a : UInt64) : ℕ → UInt64
  | 0 => a
  | n + 1 => powTwoPowWord (mulWord a a) n

/-- `powTwoPowWord` is `BF64.powTwoPow`. -/
theorem ofWord_powTwoPowWord (a : UInt64) (k : ℕ) :
    ofWord (powTwoPowWord a k) = powTwoPow (ofWord a) k := by
  induction k generalizing a with
  | zero => rfl
  | succ n ih => rw [powTwoPowWord, powTwoPow, ih, ofWord_mulWord]

/-- The inverse on words: `invItohTsujii`'s addition chain. -/
def invWord (a : UInt64) : UInt64 :=
  if a = 0 then 0 else
    let u1 := a
    let u2 := mulWord (powTwoPowWord u1 1) u1
    let u3 := mulWord (powTwoPowWord u2 1) u1
    let u6 := mulWord (powTwoPowWord u3 3) u3
    let u7 := mulWord (powTwoPowWord u6 1) u1
    let u14 := mulWord (powTwoPowWord u7 7) u7
    let u15 := mulWord (powTwoPowWord u14 1) u1
    let u30 := mulWord (powTwoPowWord u15 15) u15
    let u31 := mulWord (powTwoPowWord u30 1) u1
    let u62 := mulWord (powTwoPowWord u31 31) u31
    let u63 := mulWord (powTwoPowWord u62 1) u1
    mulWord u63 u63

/-- The inverse, on words. -/
def invFast (a : BF64) : BF64 := ofWord (invWord (toWord a))

/-- `invFast` is `BF64`'s inverse. -/
theorem invFast_eq (a : BF64) : invFast a = invItohTsujii a := by
  by_cases h : a = 0
  · subst h; rfl
  · have h' : toWord a ≠ 0 := fun h0 ↦ h (toWord_injective h0)
    simp only [invFast, invWord, invItohTsujii, h, h', ite_false, ofWord_mulWord,
      ofWord_powTwoPowWord, ofWord_toWord]

/-- `a ^ n` on words, by binary exponentiation. -/
def powWord (a : UInt64) (n : ℕ) : UInt64 :=
  if n = 0 then 1 else
    let r := powWord (mulWord a a) (n / 2)
    if n % 2 = 1 then mulWord a r else r
termination_by n
decreasing_by omega

/-- `powWord` is the natural power. -/
theorem ofWord_powWord (a : UInt64) (n : ℕ) : ofWord (powWord a n) = ofWord a ^ n := by
  apply toQuot_injective
  rw [toQuot_npow]
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    rw [powWord]
    by_cases h0 : n = 0
    · subst h0; simp only [ite_true, pow_zero]; exact toQuot_one
    · have hr := ih (n / 2) (by omega) (mulWord a a)
      rw [ofWord_mulWord, toQuot_mul, ← sq, ← pow_mul] at hr
      simp only [h0, ite_false]
      split_ifs with h1
      · rw [ofWord_mulWord, toQuot_mul, hr, ← pow_succ']
        congr 1; omega
      · rw [hr]; congr 1; omega

/-- Natural powers, on words. -/
def powFast (a : BF64) (n : ℕ) : BF64 := ofWord (powWord (toWord a) n)

/-- `powFast` is the natural power. -/
theorem powFast_eq (a : BF64) (n : ℕ) : powFast a n = a ^ n := by
  rw [powFast, ofWord_powWord, ofWord_toWord]

/-! ## The instances on words -/

/-- Multiplication on words. -/
@[instance_reducible] def instMulFast : Mul BF64 := ⟨mulFast⟩

/-- Compiled code multiplies through `instMulFast`. -/
@[csimp] theorem instMul_eq_instMulFast : @BF64.instMul = @instMulFast := by
  show (⟨BF64.mul⟩ : Mul BF64) = ⟨mulFast⟩
  congr 1; funext a b; exact (mulFast_eq a b).symm

/-- Natural powers on words. -/
@[instance_reducible] def instPowNatFast : Pow BF64 ℕ := ⟨powFast⟩

/-- Compiled code takes powers through `instPowNatFast`. -/
@[csimp] theorem instPowNat_eq_instPowNatFast : @BF64.instPowNat = @instPowNatFast := by
  show (⟨fun a n ↦ npowBinRec n a⟩ : Pow BF64 ℕ) = ⟨powFast⟩
  congr 1; funext a n; exact (powFast_eq a n).symm

/-- Inversion on words. -/
@[instance_reducible] def instInvFast : Inv BF64 := ⟨invFast⟩

/-- Compiled code inverts through `instInvFast`. -/
@[csimp] theorem instInv_eq_instInvFast : @BF64.instInv = @instInvFast := by
  show (⟨invItohTsujii⟩ : Inv BF64) = ⟨invFast⟩
  congr 1; funext a; exact (invFast_eq a).symm

/-- Division on words. -/
@[instance_reducible] def instDivFast : Div BF64 := ⟨fun a b ↦ mulFast a (invFast b)⟩

/-- Compiled code divides through `instDivFast`. -/
@[csimp] theorem instDiv_eq_instDivFast : @BF64.instDiv = @instDivFast := by
  show (⟨fun a b ↦ a * invItohTsujii b⟩ : Div BF64) = ⟨fun a b ↦ mulFast a (invFast b)⟩
  congr 1; funext a b; rw [mulFast_eq, invFast_eq]

/-- The commutative ring with multiplication and powers on words. -/
@[instance_reducible] def commRingFast : CommRing BF64 :=
  { BF64.instCommRing with
    mul := mulFast
    npow := fun n a ↦ powFast a n
    mul_assoc := fun a b c ↦ by
      show mulFast (mulFast a b) c = mulFast a (mulFast b c)
      simp only [mulFast_eq]; exact mul_assoc a b c
    one_mul := fun a ↦ by show mulFast 1 a = a; rw [mulFast_eq, one_mul]
    mul_one := fun a ↦ by show mulFast a 1 = a; rw [mulFast_eq, mul_one]
    npow_zero := fun a ↦ by show powFast a 0 = 1; rw [powFast_eq, pow_zero]
    npow_succ := fun n a ↦ by
      show powFast a (n + 1) = mulFast (powFast a n) a
      rw [powFast_eq, powFast_eq, mulFast_eq, pow_succ]
    zero_mul := fun a ↦ by show mulFast 0 a = 0; rw [mulFast_eq, zero_mul]
    mul_zero := fun a ↦ by show mulFast a 0 = 0; rw [mulFast_eq, mul_zero]
    left_distrib := fun a b c ↦ by
      show mulFast a (b + c) = mulFast a b + mulFast a c
      simp only [mulFast_eq]; exact mul_add a b c
    right_distrib := fun a b c ↦ by
      show mulFast (a + b) c = mulFast a c + mulFast b c
      simp only [mulFast_eq]; exact add_mul a b c
    mul_comm := fun a b ↦ by
      show mulFast a b = mulFast b a
      simp only [mulFast_eq]; exact mul_comm a b }

/-- Compiled code passes `commRingFast` for `BF64`'s ring. The additions are compared through
`BF64.instAdd` itself: `rfl` at the two rings' additions makes the kernel compare the rings whole,
and unfold `BF64.mul` against `mulFast`, for a minute. -/
@[csimp] theorem instCommRing_eq_commRingFast : @BF64.instCommRing = @commRingFast :=
  CommRing.ext (@rfl _ (@HAdd.hAdd _ _ _ (@instHAdd _ BF64.instAdd)))
    (funext₂ fun a b ↦ (mulFast_eq a b).symm)

/-- A field structure with the ring, the inverse, the division and the integer powers of
`BF64.instField` replaced by equal ones. The rational casts and scalar products stay those of
`BF64.instField`, over the specification's multiplication. -/
@[instance_reducible] def fieldWith (cr : CommRing BF64) (hcr : cr = BF64.instCommRing)
    (i : BF64 → BF64) (hi : i = invItohTsujii) (d : BF64 → BF64 → BF64)
    (hd : d = fun a b ↦ a * invItohTsujii b) (z : ℤ → BF64 → BF64)
    (hz : z = fun n a ↦ a ^ n) : Field BF64 :=
  { BF64.instField with
    toCommRing := cr
    inv := i
    div := d
    zpow := z
    div_eq_mul_inv := by subst hcr hi hd; exact BF64.instField.div_eq_mul_inv
    zpow_zero' := by subst hcr hi hz; exact BF64.instField.zpow_zero'
    zpow_succ' := by subst hcr hi hz; exact BF64.instField.zpow_succ'
    zpow_neg' := by subst hcr hi hz; exact BF64.instField.zpow_neg'
    exists_pair_ne := BF64.instField.exists_pair_ne
    mul_inv_cancel := by subst hcr hi hd; exact BF64.instField.mul_inv_cancel
    inv_zero := by subst hcr hi hd; exact BF64.instField.inv_zero
    nnratCast_def := by subst hcr hi hd; exact BF64.instField.nnratCast_def
    nnqsmul_def := by subst hcr hi hd; exact BF64.instField.nnqsmul_def
    ratCast_def := by subst hcr hi hd; exact BF64.instField.ratCast_def
    qsmul_def := by subst hcr hi hd; exact BF64.instField.qsmul_def }

/-- `fieldWith` is `BF64.instField`. -/
theorem fieldWith_eq (cr : CommRing BF64) (hcr : cr = BF64.instCommRing)
    (i : BF64 → BF64) (hi : i = invItohTsujii) (d : BF64 → BF64 → BF64)
    (hd : d = fun a b ↦ a * invItohTsujii b) (z : ℤ → BF64 → BF64)
    (hz : z = fun n a ↦ a ^ n) : fieldWith cr hcr i hi d hd z hz = BF64.instField := by
  subst hcr hi hd hz; rfl

/-- Integer powers on words: `powFast`, and `invFast` of it for a negative exponent. -/
def zpowFast : ℤ → BF64 → BF64
  | Int.ofNat n, a => powFast a n
  | Int.negSucc n, a => invFast (powFast a (n + 1))

/-- `zpowFast` is `BF64`'s integer power. -/
theorem zpowFast_eq (n : ℤ) (a : BF64) : zpowFast n a = a ^ n := by
  cases n with
  | ofNat n =>
    show powFast a n = a ^ (n : ℤ)
    rw [zpow_natCast, powFast_eq]
  | negSucc n =>
    show invFast (powFast a (n + 1)) = a ^ Int.negSucc n
    rw [zpow_negSucc, powFast_eq, invFast_eq]
    rfl

/-- The field with every operation on words. -/
@[instance_reducible] def fieldFast : Field BF64 :=
  fieldWith commRingFast instCommRing_eq_commRingFast.symm invFast (funext invFast_eq)
    (fun a b ↦ mulFast a (invFast b)) (funext₂ fun a b ↦ by rw [mulFast_eq, invFast_eq])
    zpowFast (funext₂ zpowFast_eq)

/-- Compiled code passes `fieldFast` for `BF64`'s field. -/
@[csimp] theorem instField_eq_fieldFast : @BF64.instField = @fieldFast :=
  (fieldWith_eq _ _ _ _ _ _ _ _).symm

end
end LeanerVM.Parameters.FastBF64
