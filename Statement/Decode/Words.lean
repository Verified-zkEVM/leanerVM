module

public import Statement.Field
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Words of `K` as `F₂`-combinations of the basis `x^c` (theorems only)

The facts about `K.ofBits` that the decoder's trace context and the novel-basis transform share:
`K.ofBits` is injective below `2^64`, turns `xor` into `+`, and the word with bits `v` is
`Σ_c v_c · x^c`.

Every declaration here is a theorem: nothing in this file can change what the extractor computes
or what a statement says, so it needs no review (`LeanVMTests.Extraction.DecodeProps` checks that
every constant of `Statement.Decode` is a proof).

Adapted from leanerVM `lean_vm/LeanVM/Protocol/Whir/Subspace.lean` (`toNat_ofBits`,
`ofBits_injOn`, `two_pow_add_eq_xor`, `ofBits_xor`, `ofBits_two_pow_add`, `ofBits_eq_sum`), branch
`mumbai` at `935b9d40`, with `basisVec c` written out as `K.ofBits (2 ^ c)`.
-/

namespace LeanVM.Extraction.Words

open LeanVM.Parameters

public section

/-- `K.ofBits 0 = 0`. -/
theorem ofBits_zero : K.ofBits 0 = 0 := rfl

/-- A word below `2^64` is read back exactly. -/
theorem toNat_ofBits {n : ℕ} (hn : n < 2 ^ 64) : (K.ofBits n).toBitVec.toNat = n := by
  simpa [K.ofBits] using hn

/-- Every element is the word of its bits. -/
theorem ofBits_toNat (a : K) : K.ofBits a.toBitVec.toNat = a := by
  apply BF64.ext
  simp [K.ofBits]

/-- The bits of an element are below `2^64`. -/
theorem toNat_lt (a : K) : a.toBitVec.toNat < 2 ^ 64 := a.toBitVec.isLt

/-- Words below `2^64` are distinct field elements. -/
theorem ofBits_injOn : Set.InjOn K.ofBits {n | n < 2 ^ 64} := by
  intro a ha b hb h
  rw [← toNat_ofBits ha, ← toNat_ofBits hb, h]

/-- A word below `2^64` is zero only when it is `0`. -/
theorem ofBits_eq_zero_iff {n : ℕ} (hn : n < 2 ^ 64) : K.ofBits n = 0 ↔ n = 0 :=
  ⟨fun h ↦ ofBits_injOn (show n < 2 ^ 64 from hn) (show 0 < 2 ^ 64 by norm_num) h,
    fun h ↦ h ▸ ofBits_zero⟩

/-- Below `2^i`, adding `2^i` sets a bit that is clear: it is the exclusive or. -/
theorem two_pow_add_eq_xor {i v : ℕ} (hv : v < 2 ^ i) : 2 ^ i + v = 2 ^ i ^^^ v := by
  have h := Nat.two_pow_add_eq_or_of_lt hv 1
  rw [mul_one] at h
  rw [h]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hj : i = j
  · subst hj
    simp [Nat.testBit_lt_two_pow hv]
  · simp [hj]

/-- Sum in `K` is bitwise exclusive or of words. -/
theorem ofBits_xor (a b : ℕ) : K.ofBits (a ^^^ b) = K.ofBits a + K.ofBits b := by
  simp only [K.ofBits, BitVec.ofNat_xor]
  rfl

/-- `x_{2^i + v} = x^i + x_v` for `v < 2^i`. -/
theorem ofBits_two_pow_add {i v : ℕ} (hv : v < 2 ^ i) :
    K.ofBits (2 ^ i + v) = K.ofBits (2 ^ i) + K.ofBits v := by
  rw [two_pow_add_eq_xor hv, ofBits_xor]

/-- The word with bits `v` is `Σ_c v_c · x^c`. -/
theorem ofBits_eq_sum {i v : ℕ} (hv : v < 2 ^ i) :
    K.ofBits v = ∑ c ∈ Finset.range i, if v.testBit c then K.ofBits (2 ^ c) else 0 := by
  induction i generalizing v with
  | zero =>
    obtain rfl : v = 0 := by simpa using hv
    simp [ofBits_zero]
  | succ i ih =>
    rw [Finset.sum_range_succ]
    by_cases hb : v.testBit i
    · have hlt : v - 2 ^ i < 2 ^ i := by
        have := Nat.ge_two_pow_of_testBit hb
        rw [pow_succ] at hv
        omega
      have hv' : v = 2 ^ i + (v - 2 ^ i) := by
        have := Nat.ge_two_pow_of_testBit hb
        omega
      have hbits : ∀ c < i, v.testBit c = (v - 2 ^ i).testBit c := by
        intro c hc
        conv_lhs => rw [hv']
        exact Nat.testBit_two_pow_add_gt hc _
      have hb' : (2 ^ i + (v - 2 ^ i)).testBit i = true := by rw [← hv']; exact hb
      rw [hv', ofBits_two_pow_add hlt, ih hlt, hb']
      simp only [ite_true]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun c hc ↦ ?_
      rw [← hv', hbits c (Finset.mem_range.mp hc)]
    · have hlt : v < 2 ^ i := by
        by_contra h
        have h1 : 2 ^ i ≤ v := not_lt.mp h
        have : v.testBit i = true := by
          have hv2 : v - 2 ^ i < 2 ^ i := by rw [pow_succ] at hv; omega
          have := Nat.testBit_two_pow_add_eq (v - 2 ^ i) i
          rw [Nat.add_sub_cancel' h1, Nat.testBit_lt_two_pow hv2] at this
          simpa using this
        exact hb this
      simp only [Bool.not_eq_true] at hb
      rw [ih hlt, hb]
      simp

end
end LeanVM.Extraction.Words
