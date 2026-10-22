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

/-- A sum of base-16 digits below 16 is below `16 ^ n`. -/
private theorem sum_digits_lt (d : ℕ → ℕ) (hd : ∀ i, d i < 16) (n : ℕ) :
    ∑ i ∈ Finset.range n, d i * 16 ^ i < 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 : d n * 16 ^ n ≤ 15 * 16 ^ n := Nat.mul_le_mul_right _ (by have := hd n; omega)
    omega

/-- Bit `4k + b` of a sum of base-16 digits below 16 is bit `b` of digit `k`. -/
private theorem testBit_sum_digits (d : ℕ → ℕ) (hd : ∀ i, d i < 16) (n k b : ℕ) (hb : b < 4) :
    (∑ i ∈ Finset.range n, d i * 16 ^ i).testBit (4 * k + b) =
      (decide (k < n) && (d k).testBit b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_comm, mul_comm, show (16 : ℕ) ^ n = 2 ^ (4 * n) by
      rw [pow_mul]; norm_num]
    rw [Nat.testBit_two_pow_mul_add _
      (sum_digits_lt d hd n |>.trans_eq (by rw [pow_mul]; norm_num))]
    split_ifs with h4
    · rw [ih]
      have hk : k < n := by omega
      simp [hk, show k < n + 1 by omega]
    · by_cases hkn : k = n
      · subst hkn
        simp [show 4 * k + b - 4 * k = b by omega]
      · have hk' : ¬ k < n + 1 := by omega
        simp only [hk', decide_false, Bool.false_and]
        apply Nat.testBit_lt_two_pow
        calc d n < 2 ^ 4 := hd n
          _ ≤ 2 ^ (4 * k + b - 4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The digit lemma for a polynomial with coefficients below 16, evaluated at 16. -/
private theorem testBit_eval_sixteen (Q : ℕ[X]) (hQ : ∀ i, Q.coeff i < 16) (k b : ℕ) (hb : b < 4) :
    (Q.eval 16).testBit (4 * k + b) = (Q.coeff k).testBit b := by
  rw [eval_eq_sum_range, testBit_sum_digits _ hQ _ _ _ hb]
  by_cases hk : k < Q.natDegree + 1
  · simp [hk]
  · simp only [hk, decide_false, Bool.false_and]
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

/-- Bit `p` of `2^r` times a digit polynomial at 16. -/
private theorem testBit_two_pow_mul_eval (Q : ℕ[X]) (hQ : ∀ i, Q.coeff i < 16) (r p : ℕ) :
    (2 ^ r * Q.eval 16).testBit p =
      (decide (r ≤ p) && (Q.coeff ((p - r) / 4)).testBit ((p - r) % 4)) := by
  rw [Nat.testBit_two_pow_mul]
  congr 1
  conv_lhs => rw [show p - r = 4 * ((p - r) / 4) + (p - r) % 4 from (Nat.div_add_mod _ _).symm]
  exact testBit_eval_sixteen Q hQ _ _ (Nat.mod_lt _ (by norm_num))

/-- The bits of a Boolean as a natural number. -/
private theorem testBit_toNat (b : Bool) (j : ℕ) : b.toNat.testBit j = (b && j == 0) := by
  cases b
  · simp
  · cases j
    · simp
    · simp only [Bool.toNat_true, Bool.true_and]
      exact Nat.testBit_lt_two_pow (by
        calc (1 : ℕ) < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (_ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The digit polynomial of residue `r`: coefficient `i` is bit `4i + r` of `x`, for `i < 8`. -/
private noncomputable def dig (x r : ℕ) : ℕ[X] :=
  ∑ i ∈ Finset.range 8, C (x.testBit (4 * i + r)).toNat * X ^ i

private theorem coeff_dig (x r k : ℕ) :
    (dig x r).coeff k = if k < 8 then (x.testBit (4 * k + r)).toNat else 0 := by
  simp only [dig, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with hk
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.mpr hk) h
  · refine Finset.sum_eq_zero fun i hi ↦ ?_
    have : k ≠ i := by simp at hi; omega
    simp [this]

private theorem coeff_dig_le (x r k : ℕ) : (dig x r).coeff k ≤ 1 := by
  rw [coeff_dig]; split_ifs <;> simp [Bool.toNat_le]

private theorem coeff_dig_eq_zero (x r k : ℕ) (hk : 8 ≤ k) : (dig x r).coeff k = 0 := by
  rw [coeff_dig]; simp [show ¬ k < 8 by omega]

private theorem coeff_dig_mul_le (x y r s k : ℕ) : (dig x r * dig y s).coeff k ≤ 8 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc ∑ i ∈ Finset.range k.succ, (dig x r).coeff i * (dig y s).coeff (k - i)
      ≤ ∑ i ∈ Finset.range k.succ, if i < 8 then 1 else 0 := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        split_ifs with hi
        · exact (Nat.mul_le_mul (coeff_dig_le x r i) (coeff_dig_le y s _)).trans (by norm_num)
        · rw [coeff_dig_eq_zero x r i (by omega)]; simp
    _ = ((Finset.range k.succ).filter (· < 8)).card := by rw [Finset.sum_boole]; simp
    _ ≤ (Finset.range 8).card := by
        refine Finset.card_le_card fun i hi ↦ ?_
        simp only [Finset.mem_filter] at hi; simpa using hi.2
    _ = 8 := by simp

/-- The all-ones digit polynomial with `n` digits. -/
private noncomputable def onesN (n : ℕ) : ℕ[X] := ∑ i ∈ Finset.range n, X ^ i

private theorem coeff_onesN (n k : ℕ) : (onesN n).coeff k = if k < n then 1 else 0 := by
  simp only [onesN, finsetSum_coeff, coeff_X_pow]
  split_ifs with hk
  · rw [Finset.sum_eq_single k] <;> simp_all [eq_comm]
  · refine Finset.sum_eq_zero fun i hi ↦ ?_
    have : k ≠ i := by simp at hi; omega
    simp [this]

/-- Masking with every fourth bit from `r` keeps the digits of residue `r`. -/
private theorem and_mask (x r : ℕ) :
    x &&& (2 ^ r * 0x11111111) = 2 ^ r * (dig x r).eval 16 := by
  apply Nat.eq_of_testBit_eq
  intro p
  have hd : ∀ i, (dig x r).coeff i < 16 := fun i ↦ (coeff_dig_le x r i).trans_lt (by norm_num)
  have he : (onesN 8).eval 16 = 0x11111111 := by simp [onesN, Finset.sum_range_succ]
  have ho : ∀ i, (onesN 8).coeff i < 16 := fun i ↦ by rw [coeff_onesN]; split_ifs <;> norm_num
  rw [Nat.testBit_and, ← he, testBit_two_pow_mul_eval _ ho, testBit_two_pow_mul_eval _ hd,
    coeff_onesN, coeff_dig]
  by_cases hrp : r ≤ p
  · simp only [hrp, decide_true, Bool.true_and]
    by_cases h8 : (p - r) / 4 < 8
    · simp only [h8, ite_true, testBit_toNat]
      have h1 : Nat.testBit 1 ((p - r) % 4) = ((p - r) % 4 == 0) := by
        simpa using testBit_toNat true ((p - r) % 4)
      rw [h1]
      by_cases hm : (p - r) % 4 = 0
      · have : 4 * ((p - r) / 4) + r = p := by omega
        simp [hm, this]
      · have hb : ((p - r) % 4 == 0) = false := by simpa using hm
        simp [hb]
    · simp [h8]
  · simp [hrp]

/-- A digit polynomial has every coefficient below 16. -/
private theorem coeff_X_pow_mul_dig_mul_lt (x y r s v k : ℕ) :
    (X ^ v * (dig x r * dig y s)).coeff k < 16 := by
  rw [coeff_X_pow_mul']
  split_ifs
  · exact (coeff_dig_mul_le x y r s _).trans_lt (by norm_num)
  · norm_num

/-- Bit `4k + t` of a product of two masked words, `r + s = t + 4v`: the parity of coefficient
`k` of the digit product shifted by `v`. -/
private theorem testBit_and_mask_mul (x y r s t v k : ℕ) (h : r + s = t + 4 * v) :
    ((x &&& (2 ^ r * 0x11111111)) * (y &&& (2 ^ s * 0x11111111))).testBit (4 * k + t) =
      decide ((X ^ v * (dig x r * dig y s)).coeff k % 2 = 1) := by
  have he : (x &&& (2 ^ r * 0x11111111)) * (y &&& (2 ^ s * 0x11111111)) =
      2 ^ t * (X ^ v * (dig x r * dig y s)).eval 16 := by
    rw [and_mask, and_mask, eval_mul, eval_mul, eval_pow, eval_X]
    rw [show (16 : ℕ) ^ v = 2 ^ (4 * v) by rw [pow_mul]; norm_num]
    rw [show 2 ^ r * eval 16 (dig x r) * (2 ^ s * eval 16 (dig y s)) =
      2 ^ (r + s) * (eval 16 (dig x r) * eval 16 (dig y s)) by rw [pow_add]; ring, h, pow_add]
    ring
  rw [he, testBit_two_pow_mul_eval _ (coeff_X_pow_mul_dig_mul_lt x y r s v) t]
  simp only [show t ≤ 4 * k + t by omega, decide_true, Bool.true_and,
    show (4 * k + t - t) / 4 = k by omega, show (4 * k + t - t) % 4 = 0 by omega, Nat.testBit_zero]

/-- Coefficient `4k + t` of `X^c` times a polynomial in `X^4`. -/
private theorem coeff_X_pow_mul_expand {R : Type*} [CommSemiring R] (Q : R[X]) (c k t : ℕ)
    (ht : t < 4) :
    (X ^ c * expand R 4 Q).coeff (4 * k + t) =
      if c % 4 = t then (X ^ (c / 4) * Q).coeff k else 0 := by
  rw [coeff_X_pow_mul', coeff_X_pow_mul']
  by_cases hc : c % 4 = t
  · simp only [hc, ite_true]
    by_cases hck : c ≤ 4 * k + t
    · have h4 : 4 ∣ 4 * k + t - c := by omega
      simp only [hck, ite_true, coeff_expand (show 0 < 4 by norm_num), h4,
        show c / 4 ≤ k by omega]
      congr 1; omega
    · simp only [hck, ite_false, show ¬ c / 4 ≤ k by omega]
  · simp only [hc, ite_false]
    split_ifs with hck
    · have h4 : ¬ 4 ∣ 4 * k + t - c := by omega
      simp only [coeff_expand (show 0 < 4 by norm_num), h4, ite_false]
    · rfl

/-- The bits of `x` below 32 as a polynomial, gathered by residue modulo 4. -/
private noncomputable def bitPoly (x : ℕ) : ℕ[X] :=
  ∑ r ∈ Finset.range 4, X ^ r * expand ℕ 4 (dig x r)

private theorem coeff_bitPoly (x i : ℕ) :
    (bitPoly x).coeff i = if i < 32 then (x.testBit i).toNat else 0 := by
  have hi : i = 4 * (i / 4) + i % 4 := (Nat.div_add_mod i 4).symm
  have ht : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [bitPoly, finsetSum_coeff, hi]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    coeff_X_pow_mul_expand _ _ _ _ ht]
  generalize i / 4 = k
  generalize hT : i % 4 = t at ht
  interval_cases t <;> simp [coeff_dig] <;> split_ifs <;> first | rfl | omega

/-- Bit `p` of the 64-bit mask with every fourth bit from `t`. -/
private theorem testBit_mask64 (t p : ℕ) (hp : p < 64) :
    (2 ^ t * 0x1111111111111111).testBit p = decide (t ≤ p ∧ (p - t) % 4 = 0) := by
  have he : (onesN 16).eval 16 = 0x1111111111111111 := by
    simp [onesN, Finset.sum_range_succ]
  have ho : ∀ i, (onesN 16).coeff i < 16 := fun i ↦ by rw [coeff_onesN]; split_ifs <;> norm_num
  rw [← he, testBit_two_pow_mul_eval _ ho, coeff_onesN]
  by_cases htp : t ≤ p
  · have h16 : (p - t) / 4 < 16 := by omega
    simp only [htp, decide_true, Bool.true_and, h16, ite_true, true_and]
    have h1 := testBit_toNat true ((p - t) % 4)
    simp only [Bool.toNat_true, Bool.true_and] at h1
    rw [h1]
    exact Bool.eq_iff_iff.mpr (by simp)
  · simp [htp]

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
  rw [UInt64.toNat_mul, UInt64.toNat_and, UInt64.toNat_and]
  apply Nat.mod_eq_of_lt
  calc (x.toNat &&& m.toNat) * (y.toNat &&& n.toNat) < 2 ^ 32 * 2 ^ 32 :=
        Nat.mul_lt_mul'' (Nat.and_lt_two_pow _ hm) (Nat.and_lt_two_pow _ hn)
    _ = 2 ^ 64 := by norm_num

/-- `clmul32` on natural numbers. -/
private theorem toNat_clmul32 (x y : UInt64) : (clmul32 x y).toNat =
    let X := x.toNat; let Y := y.toNat
    let x0 := X &&& (2 ^ 0 * 0x11111111); let x1 := X &&& (2 ^ 1 * 0x11111111)
    let x2 := X &&& (2 ^ 2 * 0x11111111); let x3 := X &&& (2 ^ 3 * 0x11111111)
    let y0 := Y &&& (2 ^ 0 * 0x11111111); let y1 := Y &&& (2 ^ 1 * 0x11111111)
    let y2 := Y &&& (2 ^ 2 * 0x11111111); let y3 := Y &&& (2 ^ 3 * 0x11111111)
    ((x0 * y0 ^^^ x1 * y3 ^^^ x2 * y2 ^^^ x3 * y1) &&& (2 ^ 0 * 0x1111111111111111)) |||
    ((x0 * y1 ^^^ x1 * y0 ^^^ x2 * y3 ^^^ x3 * y2) &&& (2 ^ 1 * 0x1111111111111111)) |||
    ((x0 * y2 ^^^ x1 * y1 ^^^ x2 * y0 ^^^ x3 * y3) &&& (2 ^ 2 * 0x1111111111111111)) |||
    ((x0 * y3 ^^^ x1 * y2 ^^^ x2 * y1 ^^^ x3 * y0) &&& (2 ^ 3 * 0x1111111111111111)) := by
  simp (disch := decide) only [clmul32, UInt64.toNat_or, UInt64.toNat_and, UInt64.toNat_xor,
    toNat_and_mul_and]
  rfl

/-- The coefficients of the product of two bit polynomials, by residue. -/
private theorem coeff_bitPoly_mul (x y k t : ℕ) (ht : t < 4) :
    (bitPoly x * bitPoly y).coeff (4 * k + t) =
      ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4,
        if (r + s) % 4 = t then (X ^ ((r + s) / 4) * (dig x r * dig y s)).coeff k else 0 := by
  rw [bitPoly, bitPoly, Finset.sum_mul_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [finsetSum_coeff]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [show X ^ r * expand ℕ 4 (dig x r) * (X ^ s * expand ℕ 4 (dig y s)) =
    X ^ (r + s) * expand ℕ 4 (dig x r * dig y s) by rw [map_mul, pow_add]; ring]
  exact coeff_X_pow_mul_expand _ _ _ _ ht

private theorem mask_select (t' t k : ℕ) (ht' : t' < 4) (ht : t < 4) :
    decide (t' ≤ 4 * k + t ∧ (4 * k + t - t') % 4 = 0) = decide (t' = t) := by
  by_cases h : t' = t
  · subst h; simp
  · simp only [h, decide_false, decide_eq_false_iff_not, not_and]
    omega

private theorem xor_parity (a b c d : ℕ) :
    (decide (a % 2 = 1) != (decide (b % 2 = 1) != (decide (c % 2 = 1) != decide (d % 2 = 1)))) =
      decide ((a + b + c + d) % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;>
  rcases Nat.mod_two_eq_zero_or_one d with hd | hd <;>
  simp [Nat.add_mod, ha, hb, hc, hd]

/-- Bit `p` of `clmul32 x y` is the parity of coefficient `p` of the product of the low 32 bits of
`x` and `y` as polynomials. -/
private theorem testBit_clmul32 (x y : UInt64) (p : ℕ) (hp : p < 64) :
    (clmul32 x y).toNat.testBit p =
      decide ((bitPoly x.toNat * bitPoly y.toNat).coeff p % 2 = 1) := by
  rw [toNat_clmul32]
  simp only [Nat.testBit_or, Nat.testBit_and, testBit_mask64 _ _ hp, Nat.testBit_xor]
  obtain ⟨k, t, ht, rfl⟩ : ∃ k t, t < 4 ∧ p = 4 * k + t :=
    ⟨p / 4, p % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod p 4).symm⟩
  rw [coeff_bitPoly_mul _ _ _ _ ht]
  simp only [mask_select _ t k (by norm_num : (0 : ℕ) < 4) ht,
    mask_select _ t k (by norm_num : (1 : ℕ) < 4) ht,
    mask_select _ t k (by norm_num : (2 : ℕ) < 4) ht,
    mask_select _ t k (by norm_num : (3 : ℕ) < 4) ht]
  interval_cases t <;>
  simp only [testBit_and_mask_mul _ _ 0 0 _ 0 k rfl, testBit_and_mask_mul _ _ 1 3 _ 1 k rfl,
    testBit_and_mask_mul _ _ 2 2 _ 1 k rfl, testBit_and_mask_mul _ _ 3 1 _ 1 k rfl,
    testBit_and_mask_mul _ _ 0 1 _ 0 k rfl, testBit_and_mask_mul _ _ 1 0 _ 0 k rfl,
    testBit_and_mask_mul _ _ 2 3 _ 1 k rfl, testBit_and_mask_mul _ _ 3 2 _ 1 k rfl,
    testBit_and_mask_mul _ _ 0 2 _ 0 k rfl, testBit_and_mask_mul _ _ 1 1 _ 0 k rfl,
    testBit_and_mask_mul _ _ 2 0 _ 0 k rfl, testBit_and_mask_mul _ _ 3 3 _ 1 k rfl,
    testBit_and_mask_mul _ _ 0 3 _ 0 k rfl, testBit_and_mask_mul _ _ 1 2 _ 0 k rfl,
    testBit_and_mask_mul _ _ 2 1 _ 0 k rfl, testBit_and_mask_mul _ _ 3 0 _ 0 k rfl] <;>
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] <;> norm_num <;>
  exact xor_parity _ _ _ _

private theorem coeff_bitPoly_mul_eq_zero (x y p : ℕ) (hp : 64 ≤ p) :
    (bitPoly x * bitPoly y).coeff p = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij ↦ ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [coeff_bitPoly, coeff_bitPoly]
  by_cases hi : ij.1 < 32
  · simp [show ¬ ij.2 < 32 by omega]
  · simp [hi]

/-- A word below `2^32` denotes its bit polynomial. -/
private theorem toPoly_eq_map_bitPoly (v : BitVec 64) (hv : v.toNat < 2 ^ 32) :
    toPoly v = (bitPoly v.toNat).map (Nat.castRingHom (ZMod 2)) := by
  ext i
  rw [toPoly_coeff, coeff_map, coeff_bitPoly]
  by_cases hi : i < 32
  · simp only [show i < 64 by omega, dite_true, hi, ite_true, BitVec.getLsb, eq_natCast]
    by_cases h : v.toNat.testBit i <;> simp [h]
  · simp only [hi, ite_false]
    split_ifs with h64 hb
    · exfalso
      have : v.toNat.testBit i = false := Nat.testBit_lt_two_pow
        (hv.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [BitVec.getLsb, this] at hb
    · simp
    · simp

private theorem bitPoly_and_low (x : ℕ) : bitPoly (x &&& 0xFFFFFFFF) = bitPoly x := by
  ext i
  rw [coeff_bitPoly, coeff_bitPoly]
  split_ifs with hi
  · congr 1
    rw [Nat.testBit_and, show (0xFFFFFFFF : ℕ) = 2 ^ 32 - 1 by norm_num,
      Nat.testBit_two_pow_sub_one]
    simp [hi]
  · rfl

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
  split_ifs with hp hb
  · simp only [BitVec.getLsb, UInt64.toNat_toBitVec, testBit_clmul32 x y p hp,
      decide_eq_true_eq] at hb
    rw [eq_natCast, ← ZMod.natCast_mod, hb]; simp
  · simp only [BitVec.getLsb, UInt64.toNat_toBitVec, testBit_clmul32 x y p hp,
      decide_eq_true_eq] at hb
    rw [eq_natCast, ← ZMod.natCast_mod, show _ % 2 = 0 by omega]; simp
  · rw [coeff_bitPoly_mul_eq_zero _ _ _ (by omega)]; simp

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

private theorem testBit_shiftRight32 (a : UInt64) (j : ℕ) :
    (a >>> 32).toNat.testBit j = a.toNat.testBit (j + 32) := by
  rw [UInt64.toNat_shiftRight, Nat.testBit_shiftRight]
  simp [Nat.add_comm]

private theorem testBit_shiftLeft32 (a : UInt64) (j : ℕ) :
    (a <<< 32).toNat.testBit j =
      (decide (32 ≤ j) && decide (j < 64) && a.toNat.testBit (j - 32)) := by
  rw [UInt64.toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  simp only [show (32 : UInt64).toNat % 64 = 32 from rfl]
  cases decide (32 ≤ j) <;> cases decide (j < 64) <;> simp [Bool.and_comm]

private theorem testBit_and_low32 (a : UInt64) (j : ℕ) :
    (a &&& 0xFFFFFFFF).toNat.testBit j = (decide (j < 32) && a.toNat.testBit j) := by
  rw [UInt64.toNat_and, Nat.testBit_and, show UInt64.toNat 0xFFFFFFFF = 2 ^ 32 - 1 from rfl,
    Nat.testBit_two_pow_sub_one, Bool.and_comm]

/-- A word is its high half times `X^32` plus its low half. -/
private theorem toPoly_word_split (a : UInt64) :
    toPoly a.toBitVec =
      toPoly (a >>> 32).toBitVec * X ^ 32 + toPoly (a &&& 0xFFFFFFFF).toBitVec := by
  ext n
  rw [coeff_add, coeff_mul_X_pow', coeff_toPoly_word, coeff_toPoly_word, coeff_toPoly_word,
    testBit_and_low32]
  rw [testBit_shiftRight32]
  by_cases h32 : 32 ≤ n
  · simp [h32, show n - 32 + 32 = n by omega, show ¬ n < 32 by omega]
  · simp [h32, show n < 32 by omega]

/-- A word shifted by 32 in both directions: the two parts of `m * X^32`. -/
private theorem toPoly_shift32_pair (m : UInt64) :
    toPoly (m >>> 32).toBitVec * X ^ 64 + toPoly (m <<< 32).toBitVec =
      toPoly m.toBitVec * X ^ 32 := by
  ext n
  rw [coeff_add, coeff_mul_X_pow', coeff_mul_X_pow', coeff_toPoly_word, coeff_toPoly_word,
    coeff_toPoly_word, testBit_shiftRight32, testBit_shiftLeft32]
  by_cases h64 : 64 ≤ n
  · have h32 : ¬ n < 64 := by omega
    simp only [h64, ite_true, show n - 64 + 32 = n - 32 by omega, h32, decide_false,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false, add_zero,
      show 32 ≤ n by omega]
  · simp only [h64, ite_false, zero_add]
    by_cases h32 : 32 ≤ n
    · simp [h32, show n < 64 by omega]
    · simp [h32]

private theorem toPoly_xor_high_low (a : UInt64) :
    toPoly ((a ^^^ (a >>> 32)) &&& 0xFFFFFFFF).toBitVec =
      toPoly (a &&& 0xFFFFFFFF).toBitVec + toPoly (a >>> 32).toBitVec := by
  ext n
  rw [coeff_add, coeff_toPoly_word, coeff_toPoly_word, coeff_toPoly_word, testBit_and_low32,
    testBit_and_low32, UInt64.toNat_xor, Nat.testBit_xor, testBit_shiftRight32]
  by_cases hn : n < 32
  · simp only [hn, decide_true, Bool.true_and]
    cases a.toNat.testBit n <;> cases a.toNat.testBit (n + 32) <;> decide
  · simp [hn, testBit_word_ge a (n + 32) (by omega)]

private theorem toPoly_high_low (a : UInt64) :
    toPoly ((a >>> 32) &&& 0xFFFFFFFF).toBitVec = toPoly (a >>> 32).toBitVec := by
  ext n
  rw [coeff_toPoly_word, coeff_toPoly_word, testBit_and_low32, testBit_shiftRight32]
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
  have hm := toPoly_shift32_pair (clmul32 (a ^^^ a >>> 32) (b ^^^ b >>> 32) ^^^ clmul32 a b ^^^
    clmul32 (a >>> 32) (b >>> 32))
  simp only [UInt64.toBitVec_xor, toPoly_xor, toPoly_clmul32, toPoly_xor_high_low,
    toPoly_high_low] at hm ⊢
  rw [toPoly_word_split a, toPoly_word_split b]
  have h2 : (2 : (ZMod 2)[X]) = 0 := ZMod2Poly.two_eq_zero
  linear_combination hm + (toPoly (a &&& 0xFFFFFFFF).toBitVec * toPoly (b &&& 0xFFFFFFFF).toBitVec +
    toPoly (a >>> 32).toBitVec * toPoly (b >>> 32).toBitVec) * X ^ 32 * h2

private theorem testBit_shiftRight_word (a s : UInt64) (hs : s.toNat < 64) (j : ℕ) :
    (a >>> s).toNat.testBit j = a.toNat.testBit (j + s.toNat) := by
  rw [UInt64.toNat_shiftRight, Nat.testBit_shiftRight, Nat.mod_eq_of_lt hs, Nat.add_comm]

private theorem testBit_shiftLeft_word (a s : UInt64) (hs : s.toNat < 64) (j : ℕ) :
    (a <<< s).toNat.testBit j =
      (decide (s.toNat ≤ j) && decide (j < 64) && a.toNat.testBit (j - s.toNat)) := by
  rw [UInt64.toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.mod_eq_of_lt hs]
  cases decide (s.toNat ≤ j) <;> cases decide (j < 64) <;> simp [Bool.and_comm]

/-- A word shifted left by `k` and right by `64 - k`: the two parts of `m * X^k`. -/
private theorem toPoly_shift_pair (m s s' : UInt64) (hk : 0 < s.toNat) (hs : s.toNat < 64)
    (hs' : s'.toNat = 64 - s.toNat) :
    toPoly (m >>> s').toBitVec * X ^ 64 + toPoly (m <<< s).toBitVec =
      toPoly m.toBitVec * X ^ s.toNat := by
  ext n
  rw [coeff_add, coeff_mul_X_pow', coeff_mul_X_pow', coeff_toPoly_word, coeff_toPoly_word,
    coeff_toPoly_word, testBit_shiftRight_word _ _ (by omega), testBit_shiftLeft_word _ _ hs, hs']
  by_cases h64 : 64 ≤ n
  · have h1 : ¬ n < 64 := by omega
    simp only [h64, ite_true, show n - 64 + (64 - s.toNat) = n - s.toNat by omega, h1,
      decide_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false, add_zero,
      show s.toNat ≤ n by omega]
  · simp only [h64, ite_false, zero_add]
    by_cases hsn : s.toNat ≤ n
    · simp [hsn, show n < 64 by omega]
    · simp [hsn]

/-- Reduce `hi · X^64 + lo` modulo `X^64 + X^4 + X^3 + X + 1`: `X^64 = X^4 + X^3 + X + 1` folds
`hi` down, and the at most four bits it pushes past `X^63` fold down once more. -/
@[inline] def reduceWords (hi lo : UInt64) : UInt64 :=
  let t := hi ^^^ (hi <<< 1) ^^^ (hi <<< 3) ^^^ (hi <<< 4)
  let o := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  lo ^^^ t ^^^ o ^^^ (o <<< 1) ^^^ (o <<< 3) ^^^ (o <<< 4)

private theorem shiftRight_eq_zero_of_lt (o s : UInt64) (ho : o.toNat < 16) (hs : 4 ≤ s.toNat)
    (hs' : s.toNat < 64) : o >>> s = 0 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hs', Nat.shiftRight_eq_div_pow]
  simp only [UInt64.toNat_zero]
  exact Nat.div_eq_of_lt (ho.trans_le (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ s.toNat := Nat.pow_le_pow_right (by norm_num) hs))

/-- `reduceWords` computes the remainder modulo `BF64.basePoly`. -/
theorem toPoly_reduceWords (hi lo : UInt64) :
    toPoly (reduceWords hi lo).toBitVec =
      (toPoly hi.toBitVec * X ^ 64 + toPoly lo.toBitVec) % BF64.basePoly := by
  have ho16 : ((hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)).toNat < 16 := by
    have h := hi.toNat_lt
    simp only [UInt64.toNat_xor, UInt64.toNat_shiftRight,
      show UInt64.toNat 63 % 64 = 63 from rfl, show UInt64.toNat 61 % 64 = 61 from rfl,
      show UInt64.toNat 60 % 64 = 60 from rfl, Nat.shiftRight_eq_div_pow]
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_ <;>
      exact Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact h.trans_le (Nat.pow_le_pow_right
        (by norm_num) (by norm_num)))
  set o := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60) with ho
  have p1 := toPoly_shift_pair hi 1 63 (by decide) (by decide) (by decide)
  have p3 := toPoly_shift_pair hi 3 61 (by decide) (by decide) (by decide)
  have p4 := toPoly_shift_pair hi 4 60 (by decide) (by decide) (by decide)
  have q1 := toPoly_shift_pair o 1 63 (by decide) (by decide) (by decide)
  have q3 := toPoly_shift_pair o 3 61 (by decide) (by decide) (by decide)
  have q4 := toPoly_shift_pair o 4 60 (by decide) (by decide) (by decide)
  rw [shiftRight_eq_zero_of_lt o 63 ho16 (by decide) (by decide)] at q1
  rw [shiftRight_eq_zero_of_lt o 61 ho16 (by decide) (by decide)] at q3
  rw [shiftRight_eq_zero_of_lt o 60 ho16 (by decide) (by decide)] at q4
  have hz : toPoly (0 : UInt64).toBitVec = 0 := toPoly_zero_eq_zero
  rw [hz, zero_mul, zero_add] at q1 q3 q4
  have hO : toPoly o.toBitVec =
      toPoly (hi >>> 63).toBitVec + toPoly (hi >>> 61).toBitVec + toPoly (hi >>> 60).toBitVec := by
    simp only [ho, UInt64.toBitVec_xor, toPoly_xor]
  have hdeg : (toPoly (reduceWords hi lo).toBitVec).degree < BF64.basePoly.degree := by
    rw [BF64.basePoly_degree]; exact toPoly_degree_lt_w (by norm_num) _
  rw [← (Polynomial.mod_eq_self_iff BF64.basePoly_ne_zero).mpr hdeg]
  symm
  apply CanonicalEuclideanDomain.mod_eq_of_eq_add_mul (q := toPoly hi.toBitVec + toPoly o.toBitVec)
    _ BF64.basePoly_ne_zero
  have h2 : (2 : (ZMod 2)[X]) = 0 := ZMod2Poly.two_eq_zero
  simp only [reduceWords, ← ho, UInt64.toBitVec_xor, toPoly_xor]
  rw [BF64.basePoly_eq]
  simp only [show UInt64.toNat 1 = 1 from rfl, show UInt64.toNat 3 = 3 from rfl,
    show UInt64.toNat 4 = 4 from rfl] at p1 p3 p4 q1 q3 q4
  linear_combination (-1 : (ZMod 2)[X]) * p1 - p3 - p4 - q1 - q3 - q4 - X ^ 64 * hO -
    (toPoly hi.toBitVec + toPoly o.toBitVec) * (1 + X + X ^ 3 + X ^ 4) * h2

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

/-- Compiled code passes `commRingFast` for `BF64`'s ring. -/
@[csimp] theorem instCommRing_eq_commRingFast : @BF64.instCommRing = @commRingFast :=
  CommRing.ext rfl (funext₂ fun a b ↦ (mulFast_eq a b).symm)

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
