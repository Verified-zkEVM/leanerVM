/-
  LeanVM.Guest.B1.Sig.SphincsDigest

  The message digest's two cells, as `verify_sig_lean_sphincs` checks them: the sum of the
  codeword indices' weights, and the index plus the marks' terms plus the unused bytes.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsPrologue

/-!
# The digest's cells as integers

* `fkWeight_eq`, `cbMul_eq`: a weight and a mark's term are `eOfNat192` of their integer;
* `sum_eOfNat192`, `sum_digits_lt`, `sum_digit`: a sum of digits in base `2^m` and its digits;
* `cellNat_eOfNat192`: the integer of a cell below `2^128`;
* `encSum_eq`, `boundSum_eq`: the running encoding and the bound, at the end, as integers.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

theorem word_eq_eOfNat192 {n : Nat} (h : n < 2 ^ 64) : word n 0 0 = eOfNat192 n := by
  rw [word_eq_eOfNat, eOfNat192_of_lt h]

theorem word_hi_eq_eOfNat192 {n : Nat} (h : n < 2 ^ 64) : word 0 n 0 = eOfNat192 (2 ^ 64 * n) := by
  rw [eOfNat192_two_pow_64_mul h, word, ofBits_zero]

theorem fkWeight_eq {t w : Nat} (ht : t < 256) (hw : w < 16) :
    fkWeight t w = eOfNat192 (t * 2 ^ (8 * w)) := by
  unfold fkWeight
  split
  · rw [word_eq_eOfNat192]
    calc t * 2 ^ (8 * w) < 256 * 2 ^ (8 * w) := by
          exact Nat.mul_lt_mul_of_pos_right ht (Nat.two_pow_pos _)
      _ ≤ 2 ^ 64 := by
          rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [word_hi_eq_eOfNat192]
    · congr 1
      rw [show 8 * w = 64 + 8 * (w - 8) by omega, pow_add]
      ring
    · calc t * 2 ^ (8 * (w - 8)) < 256 * 2 ^ (8 * (w - 8)) := by
            exact Nat.mul_lt_mul_of_pos_right ht (Nat.two_pow_pos _)
        _ ≤ 2 ^ 64 := by
            rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem cbMul_eq {a k m : Nat} (ha : a < 2 ^ m) (hk : k + m ≤ 128) (hlo : k < 64 → k + m ≤ 64) :
    cbMul a k = eOfNat192 (a * 2 ^ k) := by
  unfold cbMul
  split
  · rename_i hk64
    rw [word_eq_eOfNat192]
    calc a * 2 ^ k < 2 ^ m * 2 ^ k := Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos _)
      _ ≤ 2 ^ 64 := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · rename_i hk64
    rw [word_hi_eq_eOfNat192]
    · congr 1
      rw [show k = 64 + (k - 64) by omega, pow_add, Nat.add_sub_cancel_left]
      ring
    · calc a * 2 ^ (k - 64) < 2 ^ m * 2 ^ (k - 64) := Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos _)
        _ ≤ 2 ^ 64 := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ## Sums of digits -/

theorem sum_digits_lt (f : Nat → Nat) (m : Nat) (hf : ∀ k, f k < 2 ^ m) :
    ∀ n, ∑ k ∈ Finset.range n, f k * 2 ^ (m * k) < 2 ^ (m * n)
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ]
      have ih := sum_digits_lt f m hf n
      have h1 : f n * 2 ^ (m * n) ≤ (2 ^ m - 1) * 2 ^ (m * n) :=
        Nat.mul_le_mul_right _ (by have := hf n; omega)
      have h2 : (2 ^ m - 1) * 2 ^ (m * n) + 2 ^ (m * n) = 2 ^ (m * (n + 1)) := by
        rw [Nat.sub_mul, one_mul, Nat.mul_succ, pow_add, mul_comm (2 ^ m)]
        have : 2 ^ (m * n) ≤ 2 ^ (m * n) * 2 ^ m :=
          Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
        omega
      omega

theorem sum_eOfNat192 (f : Nat → Nat) (m b : Nat) (hf : ∀ k, f k < 2 ^ m) :
    ∀ n, ∑ k ∈ Finset.range n, eOfNat192 (f k * 2 ^ (b + m * k)) =
      eOfNat192 (2 ^ b * ∑ k ∈ Finset.range n, f k * 2 ^ (m * k))
  | 0 => by simp [eOfNat192_zero]
  | n + 1 => by
      rw [Finset.sum_range_succ, sum_eOfNat192 f m b hf n, Finset.sum_range_succ]
      have hlt := sum_digits_lt f m hf n
      have hS : 2 ^ b * ∑ k ∈ Finset.range n, f k * 2 ^ (m * k) < 2 ^ (b + m * n) := by
        rw [pow_add]
        exact Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos _)
      rw [show f n * 2 ^ (b + m * n) = 2 ^ (b + m * n) * f n by ring, eOfNat192_add_shift hS]
      congr 1
      rw [pow_add]
      ring

/-- **A digit of a sum of digits.** -/
theorem sum_digit (f : Nat → Nat) (m : Nat) (hf : ∀ k, f k < 2 ^ m) :
    ∀ n j, j < n → (∑ k ∈ Finset.range n, f k * 2 ^ (m * k)) / 2 ^ (m * j) % 2 ^ m = f j
  | 0, _, h => absurd h (by omega)
  | n + 1, j, hj => by
      rw [Finset.sum_range_succ]
      rcases Nat.lt_or_ge j n with h | h
      · have hlt := sum_digits_lt f m hf n
        have e : f n * 2 ^ (m * n) = 2 ^ (m * j) * (2 ^ m * (f n * 2 ^ (m * (n - j - 1)))) := by
          have hn : m * n = m * j + m + m * (n - j - 1) := by
            rw [← Nat.mul_succ, ← Nat.mul_add]
            congr 1
            omega
          rw [hn, pow_add, pow_add]
          ring
        rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left]
        exact sum_digit f m hf n j h
      · have hjn : j = n := by omega
        subst hjn
        have hlt := sum_digits_lt f m hf j
        rw [mul_comm (f j), Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt hlt, zero_add, Nat.mod_eq_of_lt (hf j)]

theorem cellNat_eOfNat192 {V : Nat} (h : V < 2 ^ 128) : cellNat (eOfNat192 V) = V := by
  simp only [cellNat, eOfNat192, ofLimbs_limb0, ofLimbs_limb1, kToNat_ofBits]
  have : V = V % 2 ^ 64 + 2 ^ 64 * (V / 2 ^ 64) := (Nat.mod_add_div V _).symm
  have h2 : V / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc V < 2 ^ 128 := h
      _ = 2 ^ 64 * 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt h2]
  omega

theorem sum_range_two_mul {M : Type} [AddCommMonoid M] (g : Nat → M) :
    ∀ n, ∑ k ∈ Finset.range (2 * n), g k = ∑ c ∈ Finset.range n, (g (2 * c) + g (2 * c + 1))
  | 0 => by simp
  | n + 1 => by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        sum_range_two_mul g n, Finset.sum_range_succ, add_assoc]

/-! ## The two cells -/

/-- The codeword index of sub-tree `w % 2` of coordinate `w / 2`. -/
noncomputable def wT (σ : Val) (w : Nat) : Nat := cT σ (w / 2) (w % 2)

/-- The child of sub-tree `w % 2` of coordinate `w / 2`. -/
noncomputable def wA (σ : Val) (w : Nat) : Nat := cA σ (w / 2) (w % 2)

/-- The integer the running encoding sums to. -/
noncomputable def encNat (σ : Val) : Nat := ∑ w ∈ Finset.range 16, wT σ w * 2 ^ (8 * w)

/-- The marks' integer above the index: the super-children from bit `26`, the children from `58`. -/
noncomputable def marksNat (σ : Val) : Nat :=
  2 ^ 26 * ∑ c ∈ Finset.range 8, cS σ c * 2 ^ (4 * c) +
    2 ^ 58 * ∑ w ∈ Finset.range 16, wA σ w * 2 ^ (3 * w)

theorem encSum_eq {σ : Val} (hT : ∀ w < 16, wT σ w < 256) :
    ∑ k ∈ Finset.range 8, encTerm σ k = eOfNat192 (encNat σ) := by
  have h1 : ∑ k ∈ Finset.range 8, encTerm σ k =
      ∑ w ∈ Finset.range 16, eOfNat192 (min (wT σ w) 255 * 2 ^ (0 + 8 * w)) := by
    rw [show 16 = 2 * 8 from rfl, sum_range_two_mul]
    apply Finset.sum_congr rfl
    intro c hc
    have hc8 := Finset.mem_range.mp hc
    have t0 := hT (2 * c) (by omega)
    have t1 := hT (2 * c + 1) (by omega)
    simp only [wT, show 2 * c / 2 = c by omega, show (2 * c + 1) / 2 = c by omega,
      show 2 * c % 2 = 0 by omega, show (2 * c + 1) % 2 = 1 by omega] at t0 t1 ⊢
    rw [encTerm, fkWeight_eq t0 (by omega), fkWeight_eq t1 (by omega), Nat.zero_add, Nat.zero_add,
      Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
  rw [h1, sum_eOfNat192 (fun w => min (wT σ w) 255) 8 0 (fun k =>
    lt_of_le_of_lt (Nat.min_le_right (wT σ k) 255) (by norm_num)) 16, pow_zero, one_mul, encNat]
  exact congrArg eOfNat192 (Finset.sum_congr rfl fun w hw => by
    rw [Nat.min_eq_left (by have := hT w (Finset.mem_range.mp hw); omega)])

theorem boundSum_eq {σ : Val} (hS : ∀ c < 8, cS σ c < 16) (hA : ∀ w < 16, wA σ w < 8) :
    ∑ k ∈ Finset.range 8, boundTerm σ k = eOfNat192 (marksNat σ) := by
  have e1 : ∑ k ∈ Finset.range 8, boundTerm σ k =
      ∑ c ∈ Finset.range 8, eOfNat192 (min (cS σ c) 15 * 2 ^ (26 + 4 * c)) +
        ∑ w ∈ Finset.range 16, eOfNat192 (min (wA σ w) 7 * 2 ^ (58 + 3 * w)) := by
    rw [show 16 = 2 * 8 from rfl, sum_range_two_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    have hc8 := Finset.mem_range.mp hc
    have a0 := hA (2 * c) (by omega)
    have a1 := hA (2 * c + 1) (by omega)
    have s0 := hS c hc8
    simp only [wA, show 2 * c / 2 = c by omega, show (2 * c + 1) / 2 = c by omega,
      show 2 * c % 2 = 0 by omega, show (2 * c + 1) % 2 = 1 by omega] at a0 a1 ⊢
    rw [boundTerm, cbMul_eq (m := 3) (by simpa using a0) (by omega) (by omega),
      cbMul_eq (m := 3) (by simpa using a1) (by omega) (by omega),
      cbMul_eq (m := 4) (by simpa using s0) (by omega) (by omega),
      Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    abel
  rw [e1, sum_eOfNat192 (fun c => min (cS σ c) 15) 4 26 (fun k =>
      lt_of_le_of_lt (Nat.min_le_right (cS σ k) 15) (by norm_num)) 8,
    sum_eOfNat192 (fun w => min (wA σ w) 7) 3 58 (fun k =>
      lt_of_le_of_lt (Nat.min_le_right (wA σ k) 7) (by norm_num)) 16]
  have hlt := sum_digits_lt (fun c => min (cS σ c) 15) 4 (fun k =>
      lt_of_le_of_lt (Nat.min_le_right (cS σ k) 15) (by norm_num)) 8
  have h2 : 2 ^ 26 * ∑ k ∈ Finset.range 8, min (cS σ k) 15 * 2 ^ (4 * k) < 2 ^ 58 := by
    calc _ < 2 ^ 26 * 2 ^ (4 * 8) := Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos _)
      _ = 2 ^ 58 := by norm_num
  rw [eOfNat192_add_shift h2, marksNat]
  refine congrArg eOfNat192 (congrArg₂ (· + ·) (congrArg (2 ^ 26 * ·) (Finset.sum_congr rfl
    fun c hc => ?_)) (congrArg (2 ^ 58 * ·) (Finset.sum_congr rfl fun w hw => ?_)))
  · rw [Nat.min_eq_left (by have := hS c (Finset.mem_range.mp hc); omega)]
  · rw [Nat.min_eq_left (by have := hA w (Finset.mem_range.mp hw); omega)]

/-- A digit below a bound `2^K` is the low part's. -/
theorem digit_low {S R K m j : Nat} (hj : m * j + m ≤ K) :
    (S + 2 ^ K * R) / 2 ^ (m * j) % 2 ^ m = S / 2 ^ (m * j) % 2 ^ m := by
  have e : 2 ^ K * R = 2 ^ (m * j) * (2 ^ m * (2 ^ (K - m * j - m) * R)) := by
    rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, show m * j + m + (K - m * j - m) = K by omega]
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left]

theorem sum_min_eq (f : Nat → Nat) (m n : Nat) (hf : ∀ k < n, f k < 2 ^ m) :
    ∑ k ∈ Finset.range n, f k * 2 ^ (m * k) =
      ∑ k ∈ Finset.range n, min (f k) (2 ^ m - 1) * 2 ^ (m * k) :=
  Finset.sum_congr rfl fun k hk => by
    rw [Nat.min_eq_left (by have := hf k (Finset.mem_range.mp hk); omega)]

theorem min_lt (a m : Nat) : min a (2 ^ m - 1) < 2 ^ m :=
  lt_of_le_of_lt (Nat.min_le_right _ _) (by have := Nat.two_pow_pos m; omega)

/-- **A digit of a sum of digits**, the digits bounded below `n`. -/
theorem sum_digit' (f : Nat → Nat) (m n : Nat) (hf : ∀ k < n, f k < 2 ^ m) {j : Nat} (hj : j < n) :
    (∑ k ∈ Finset.range n, f k * 2 ^ (m * k)) / 2 ^ (m * j) % 2 ^ m = f j := by
  rw [sum_min_eq f m n hf, sum_digit (fun k => min (f k) (2 ^ m - 1)) m (fun k => min_lt _ _) n j hj,
    Nat.min_eq_left (by have := hf j hj; omega)]

theorem sum_digits_lt' (f : Nat → Nat) (m n : Nat) (hf : ∀ k < n, f k < 2 ^ m) :
    ∑ k ∈ Finset.range n, f k * 2 ^ (m * k) < 2 ^ (m * n) := by
  rw [sum_min_eq f m n hf]
  exact sum_digits_lt _ m (fun k => min_lt _ _) n

/-- **The bound's digits**: the index, the super-children and the children. -/
theorem bound_digits {σ : Val} (hS : ∀ c < 8, cS σ c < 16) (hA : ∀ w < 16, wA σ w < 8) {idx N : Nat}
    (hidx : idx < 2 ^ 26) (hN : N < 2 ^ 22) :
    idx + marksNat σ + 2 ^ 106 * N < 2 ^ 128 ∧
      (idx + marksNat σ + 2 ^ 106 * N) % 2 ^ 26 = idx ∧
      (∀ c < 8, (idx + marksNat σ + 2 ^ 106 * N) / 2 ^ (26 + 4 * c) % 2 ^ 4 = cS σ c) ∧
      (∀ w < 16, (idx + marksNat σ + 2 ^ 106 * N) / 2 ^ (58 + 3 * w) % 2 ^ 3 = wA σ w) := by
  set S := ∑ c ∈ Finset.range 8, cS σ c * 2 ^ (4 * c) with hSdef
  set A := ∑ w ∈ Finset.range 16, wA σ w * 2 ^ (3 * w) with hAdef
  have hSl : S < 2 ^ 32 := sum_digits_lt' (cS σ) 4 8 (fun k hk => by simpa using hS k hk)
  have hAl : A < 2 ^ 48 := sum_digits_lt' (wA σ) 3 16 (fun k hk => by simpa using hA k hk)
  have hV : idx + marksNat σ + 2 ^ 106 * N = idx + 2 ^ 26 * S + 2 ^ 58 * A + 2 ^ 106 * N := by
    rw [marksNat]; ring
  rw [hV]
  have e26 : idx + 2 ^ 26 * S + 2 ^ 58 * A + 2 ^ 106 * N =
      idx + 2 ^ 26 * (S + 2 ^ 32 * (A + 2 ^ 48 * N)) := by ring
  have e58 : idx + 2 ^ 26 * S + 2 ^ 58 * A + 2 ^ 106 * N =
      (idx + 2 ^ 26 * S) + 2 ^ 58 * (A + 2 ^ 48 * N) := by ring
  refine ⟨by omega, ?_, fun c hc => ?_, fun w hw => ?_⟩
  · rw [e26, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hidx]
  · rw [e26, pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hidx, Nat.zero_add, digit_low (K := 32) (by omega)]
    exact sum_digit' (cS σ) 4 8 (fun k hk => by simpa using hS k hk) hc
  · have hlo : idx + 2 ^ 26 * S < 2 ^ 58 := by omega
    rw [e58, pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hlo, Nat.zero_add, digit_low (K := 48) (by omega)]
    exact sum_digit' (wA σ) 3 16 (fun k hk => by simpa using hA k hk) hw

/-- **The encoding's digits.** -/
theorem enc_digits {σ : Val} (hT : ∀ w < 16, wT σ w < 256) :
    encNat σ < 2 ^ 128 ∧ ∀ w < 16, encNat σ / 2 ^ (8 * w) % 2 ^ 8 = wT σ w :=
  ⟨sum_digits_lt' (wT σ) 8 16 (fun k hk => by simpa using hT k hk),
    fun w hw => sum_digit' (wT σ) 8 16 (fun k hk => by simpa using hT k hk) hw⟩

end
end LeanVM.Guest.B1.Sig
