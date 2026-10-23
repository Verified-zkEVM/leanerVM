/-
  LeanVM.Guest.B1.Sig.SphincsSpecComplete

  The Spec side of `verify_sig_lean_sphincs`'s completeness: the hints a signature and the message
  digest's cells give, the digest's cells the sums of their terms, and the openings the frame holds.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsEndComplete
public import LeanVM.Guest.B1.Sig.SphincsPrologueComplete

/-!
# The Spec side

* `digits_mod`: the base-`2^m` digits of `n` sum to `n mod 2^(m k)`;
* `encSumF`, `boundSumF`, `bound_cellF`: the encoding's and the bound's terms of digits as
  `u192` words;
* `cell17_eq`, `cell18_eq`: the digest's cells are the sums of the terms of their digits;
* `subHOf`, `coordHOf`: a coordinate's hints from its opening and the digest's marks;
* `coordOpening_eq`: the opening a coordinate's valuation holds is the hinted one.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat gen)
open Sphincs

@[expose] public section

/-- The base-`2^m` digits of `n` sum to `n mod 2^(m k)`. -/
theorem digits_mod (m n : Nat) : ∀ k,
    ∑ i ∈ Finset.range k, n / 2 ^ (m * i) % 2 ^ m * 2 ^ (m * i) = n % 2 ^ (m * k)
  | 0 => by simp [Nat.mod_one]
  | k + 1 => by
      rw [Finset.sum_range_succ, digits_mod m n k, Nat.mul_succ, pow_add, Nat.mod_mul]
      ring

/-! ## The terms of digits -/

/-- **The encoding's terms of digits `T`.** -/
theorem encSumF (T : Nat → Nat) (hT : ∀ w < 16, T w < 256) :
    ∑ k ∈ Finset.range 8, (fkWeight (T (2 * k)) (2 * k) + fkWeight (T (2 * k + 1)) (2 * k + 1)) =
      eOfNat192 (∑ w ∈ Finset.range 16, T w * 2 ^ (8 * w)) := by
  have h1 : ∑ k ∈ Finset.range 8, (fkWeight (T (2 * k)) (2 * k) + fkWeight (T (2 * k + 1)) (2 * k + 1)) =
      ∑ w ∈ Finset.range 16, eOfNat192 (min (T w) 255 * 2 ^ (0 + 8 * w)) := by
    rw [show 16 = 2 * 8 from rfl, sum_range_two_mul]
    apply Finset.sum_congr rfl
    intro c hc
    have hc8 := Finset.mem_range.mp hc
    have t0 := hT (2 * c) (by omega)
    have t1 := hT (2 * c + 1) (by omega)
    rw [fkWeight_eq t0 (by omega), fkWeight_eq t1 (by omega), Nat.zero_add, Nat.zero_add,
      Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
  rw [h1, sum_eOfNat192 (fun w => min (T w) 255) 8 0 (fun k =>
    lt_of_le_of_lt (Nat.min_le_right (T k) 255) (by norm_num)) 16, pow_zero, one_mul]
  exact congrArg eOfNat192 (Finset.sum_congr rfl fun w hw => by
    rw [Nat.min_eq_left (by have := hT w (Finset.mem_range.mp hw); omega)])

/-- The marks' integer of digits `S` (super-children) and `A` (children). -/
def marksF (S A : Nat → Nat) : Nat :=
  2 ^ 26 * ∑ c ∈ Finset.range 8, S c * 2 ^ (4 * c) + 2 ^ 58 * ∑ w ∈ Finset.range 16, A w * 2 ^ (3 * w)

/-- **The bound's terms of digits.** -/
theorem boundSumF (S A : Nat → Nat) (hS : ∀ c < 8, S c < 16) (hA : ∀ w < 16, A w < 8) :
    ∑ k ∈ Finset.range 8, (cbMul (A (2 * k)) (58 + 3 * (2 * k)) + cbMul (A (2 * k + 1)) (58 + 3 * (2 * k + 1)) +
      cbMul (S k) (26 + 4 * k)) = eOfNat192 (marksF S A) := by
  have e1 : ∑ k ∈ Finset.range 8, (cbMul (A (2 * k)) (58 + 3 * (2 * k)) +
      cbMul (A (2 * k + 1)) (58 + 3 * (2 * k + 1)) + cbMul (S k) (26 + 4 * k)) =
      ∑ c ∈ Finset.range 8, eOfNat192 (min (S c) 15 * 2 ^ (26 + 4 * c)) +
        ∑ w ∈ Finset.range 16, eOfNat192 (min (A w) 7 * 2 ^ (58 + 3 * w)) := by
    rw [show 16 = 2 * 8 from rfl, sum_range_two_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    have hc8 := Finset.mem_range.mp hc
    have a0 := hA (2 * c) (by omega)
    have a1 := hA (2 * c + 1) (by omega)
    have s0 := hS c hc8
    rw [cbMul_eq (m := 3) (by simpa using a0) (by omega) (by omega),
      cbMul_eq (m := 3) (by simpa using a1) (by omega) (by omega),
      cbMul_eq (m := 4) (by simpa using s0) (by omega) (by omega),
      Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    abel
  rw [e1, sum_eOfNat192 (fun c => min (S c) 15) 4 26 (fun k =>
      lt_of_le_of_lt (Nat.min_le_right (S k) 15) (by norm_num)) 8,
    sum_eOfNat192 (fun w => min (A w) 7) 3 58 (fun k =>
      lt_of_le_of_lt (Nat.min_le_right (A k) 7) (by norm_num)) 16]
  have hlt := sum_digits_lt (fun c => min (S c) 15) 4 (fun k =>
      lt_of_le_of_lt (Nat.min_le_right (S k) 15) (by norm_num)) 8
  have h2 : 2 ^ 26 * ∑ k ∈ Finset.range 8, min (S k) 15 * 2 ^ (4 * k) < 2 ^ 58 := by
    calc _ < 2 ^ 26 * 2 ^ (4 * 8) := Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos _)
      _ = 2 ^ 58 := by norm_num
  rw [eOfNat192_add_shift h2, marksF]
  refine congrArg eOfNat192 (congrArg₂ (· + ·) (congrArg (2 ^ 26 * ·) (Finset.sum_congr rfl
    fun c hc => ?_)) (congrArg (2 ^ 58 * ·) (Finset.sum_congr rfl fun w hw => ?_)))
  · rw [Nat.min_eq_left (by have := hS c (Finset.mem_range.mp hc); omega)]
  · rw [Nat.min_eq_left (by have := hA w (Finset.mem_range.mp hw); omega)]

/-- **The bound's cell**: the index, the unused bytes' word at bit `106` and the marks. -/
theorem bound_cellF {S A : Nat → Nat} (hS : ∀ c < 8, S c < 16) (hA : ∀ w < 16, A w < 8) {idx N : Nat}
    (hidx : idx < 2 ^ 26) (hN : N < 2 ^ 22) :
    eOfNat idx + word 0 (N * 2 ^ 42) 0 + eOfNat192 (marksF S A) =
      eOfNat192 (idx + marksF S A + 2 ^ 106 * N) := by
  have hSl : ∑ c ∈ Finset.range 8, S c * 2 ^ (4 * c) < 2 ^ 32 :=
    sum_digits_lt' S 4 8 (fun k hk => by simpa using hS k hk)
  have hAl : ∑ w ∈ Finset.range 16, A w * 2 ^ (3 * w) < 2 ^ 48 :=
    sum_digits_lt' A 3 16 (fun k hk => by simpa using hA k hk)
  have hm : marksF S A = 2 ^ 26 * (∑ c ∈ Finset.range 8, S c * 2 ^ (4 * c) +
      2 ^ 32 * ∑ w ∈ Finset.range 16, A w * 2 ^ (3 * w)) := by
    rw [marksF]; ring
  rw [← eOfNat192_of_lt (by omega), word_hi_eq_eOfNat192 (by omega), add_right_comm, hm,
    eOfNat192_add_shift (by omega), ← hm, show 2 ^ 64 * (N * 2 ^ 42) = 2 ^ 106 * N by ring,
    eOfNat192_add_shift (by rw [hm]; omega)]

/-! ## The digest's cells -/

/-- The codeword index of sub-tree `w % 2` of coordinate `w / 2` in the first cell's integer. -/
def dT (N17 w : Nat) : Nat := N17 / 2 ^ (8 * w) % 2 ^ 8

/-- The super-child of coordinate `c` in the second cell's integer. -/
def dS (N18 c : Nat) : Nat := N18 / 2 ^ (26 + 4 * c) % 2 ^ 4

/-- The child of sub-tree `w % 2` of coordinate `w / 2` in the second cell's integer. -/
def dA (N18 w : Nat) : Nat := N18 / 2 ^ (58 + 3 * w) % 2 ^ 3

theorem dT_lt (N17 w : Nat) : dT N17 w < 256 := Nat.mod_lt _ (by norm_num)

theorem dS_lt (N18 c : Nat) : dS N18 c < 16 := Nat.mod_lt _ (by norm_num)

theorem dA_lt (N18 w : Nat) : dA N18 w < 8 := Nat.mod_lt _ (by norm_num)

/-- **The first cell's integer is its digits'.** -/
theorem cell17_eq {N17 : Nat} (h : N17 < 2 ^ 128) :
    ∑ w ∈ Finset.range 16, dT N17 w * 2 ^ (8 * w) = N17 := by
  simp only [dT]
  rw [digits_mod 8 N17 16, Nat.mod_eq_of_lt (by simpa using h)]

/-- **The second cell's integer is its index's, its marks' and its unused bits'.** -/
theorem cell18_eq (N18 : Nat) :
    N18 % 2 ^ 26 + marksF (dS N18) (dA N18) + 2 ^ 106 * (N18 / 2 ^ 106) = N18 := by
  have eS : ∑ c ∈ Finset.range 8, dS N18 c * 2 ^ (4 * c) = N18 / 2 ^ 26 % 2 ^ 32 := by
    rw [show (2 : Nat) ^ 32 = 2 ^ (4 * 8) by norm_num, ← digits_mod 4 (N18 / 2 ^ 26) 8]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dS, Nat.div_div_eq_div_mul, ← pow_add]
  have eA : ∑ w ∈ Finset.range 16, dA N18 w * 2 ^ (3 * w) = N18 / 2 ^ 58 % 2 ^ 48 := by
    rw [show (2 : Nat) ^ 48 = 2 ^ (3 * 16) by norm_num, ← digits_mod 3 (N18 / 2 ^ 58) 16]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [dA, Nat.div_div_eq_div_mul, ← pow_add]
  rw [marksF, eS, eA]
  norm_num
  omega

/-! ## The hints of an opening -/

/-- A sub-tree's hints: its codeword index `t`, its child `a`, its opening's chain values and path. -/
def subHOf (op : SubOpening) (t a : Nat) : SubH :=
  ⟨t, a, fun i => if h : i < 6 then cellOf128 (op.values ⟨i, h⟩) else 0,
    fun l => if h : l < 3 then cellOf128 (op.path ⟨l, h⟩) else 0⟩

/-- A coordinate's hints: its super-child `s`, its opening's top path, its sub-trees'. -/
def coordHOf (op : CoordOpening) (s t0 a0 t1 a1 : Nat) : CoordH :=
  ⟨s, fun l => if h : l < 4 then cellOf128 (op.top ⟨l, h⟩) else 0, subHOf (op.sub 0) t0 a0,
    subHOf (op.sub 1) t1 a1⟩

theorem canon_dite {p : Prop} [Decidable p] {f : p → BitVec 128} :
    IsCanonical128 (if h : p then cellOf128 (f h) else 0) := by
  split
  · exact isCanonical128_cellOf128 _
  · exact canon_zero

theorem subHOf_ok (op : SubOpening) {t a : Nat} (ht : t < 256) (ha : a < 8) : (subHOf op t a).OK :=
  ⟨ht, ha, fun _ => canon_dite, fun _ => canon_dite⟩

theorem coordHOf_ok (op : CoordOpening) {s t0 a0 t1 a1 : Nat} (hs : s < 16) (ht0 : t0 < 256)
    (ha0 : a0 < 8) (ht1 : t1 < 256) (ha1 : a1 < 8) : (coordHOf op s t0 a0 t1 a1).OK :=
  ⟨hs, fun _ => canon_dite, subHOf_ok _ ht0 ha0, subHOf_ok _ ht1 ha1⟩

theorem sv_dite {n : Nat} {f : Fin n → BitVec 128} (i : Fin n) :
    sv (if h : i.val < n then cellOf128 (f ⟨i.val, h⟩) else 0) = f i := by
  simp only [i.isLt, ↓reduceDIte]
  exact cellVal_cellOf128 _

/-- **A sub-tree's opening, read off its valuation**, is the hinted one. -/
theorem subOpening_eq {σ : Val} {encIn boundIn : E} {c j : Nat} {enc : Option V} {b : Nat}
    {op : SubOpening} {t a : Nat} (ht : t < 256) (ha : a < 8)
    (h : SubPost encIn boundIn c j enc b (subHOf op t a) σ) : subOpening σ c j enc b = op := by
  obtain ⟨h0, -, h6, hv, hs, hs2, -⟩ := h
  dsimp only [subHOf] at h0 h6 hv hs hs2
  have ea : subA σ b = a := logG_eq ha (by norm_num) h0
  have et : subT σ b = t := logG_eq ht (by norm_num) h6
  cases op with
  | mk values path =>
    simp only [subOpening, SubOpening.mk.injEq]
    refine ⟨funext fun i => ?_, funext fun l => ?_⟩
    · rw [subVal, et, hv i.val i.isLt]
      exact sv_dite i
    · unfold subSib
      rw [ea]
      by_cases hl : l.val < 2
      · simp only [hl, ↓reduceIte]
        have := hs l.val hl
        rw [show (fun a => word (j * 2 ^ 39 + a * 2 ^ 40) 0 0) = subMark j from rfl, this]
        exact sv_dite l
      · simp only [hl, ↓reduceIte]
        have hl2 : l = ⟨2, by decide⟩ := Fin.ext (by have := l.isLt; simp [subHeight] at this ⊢; omega)
        subst hl2
        by_cases hq : a / 2 ^ 2 = 0 <;> simp only [hq, ↓reduceIte] at hs2 ⊢ <;> rw [hs2] <;>
          exact sv_dite (n := 3) ⟨2, by decide⟩

/-- **A coordinate's opening, read off its valuation**, is the hinted one. -/
theorem coordOpening_eq {σ : Val} {encIn boundIn : E} {c : Nat} {enc : Option V} {bound : V} {b : Nat}
    {op : CoordOpening} {s t0 a0 t1 a1 : Nat} (hs : s < 16) (ht0 : t0 < 256) (ha0 : a0 < 8)
    (ht1 : t1 < 256) (ha1 : a1 < 8)
    (h : CoordPost encIn boundIn c enc bound b (coordHOf op s t0 a0 t1 a1) σ) :
    coordOpening σ c enc bound b = op := by
  obtain ⟨h0, -, hs0, hs1, ht, ht3, -⟩ := h
  dsimp only [coordHOf] at h0 ht ht3 hs0 hs1
  have es : coordS σ b = s := logG_eq hs (by norm_num) h0
  cases op with
  | mk sub top =>
    simp only [coordOpening, CoordOpening.mk.injEq]
    refine ⟨funext fun j => ?_, funext fun l => ?_⟩
    · rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with rfl | rfl
      · exact subOpening_eq ht0 ha0 hs0
      · exact subOpening_eq ht1 ha1 hs1
    · unfold topSib
      rw [es]
      by_cases hl : l.val < 3
      · simp only [hl, ↓reduceIte]
        have := ht l.val hl
        rw [show (fun s => word (c * hiMul + s * 2 ^ 35) 0 0) = coordMark c from rfl, this]
        exact sv_dite l
      · simp only [hl, ↓reduceIte]
        have hl3 : l = ⟨3, by decide⟩ := Fin.ext (by have := l.isLt; simp [topHeight] at this ⊢; omega)
        subst hl3
        by_cases hq : s / 2 ^ 3 = 0 <;> simp only [hq, ↓reduceIte] at ht3 ⊢ <;> rw [ht3] <;>
          exact sv_dite (n := 4) ⟨3, by decide⟩

end
end LeanVM.Guest.B1.Sig
