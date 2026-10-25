import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.GCongr

/-!
# A quadratic transfer term, linear under a query cap

The random-permutation transfers and the sponge's indifferentiability cost `q² / 2^n` for `q`
permutation calls, with `n` about `508`. Under a cap `q ≤ 2^k` this is at most `q · 2^-(n - k)`, a
term linear in `q` (`sq_div_le_mul_inv_pow`, with `n = k + e`), which the end statements state in
its place.
-/

open scoped ENNReal

namespace Common

/-- **A quadratic term, linear under a cap**: for `q ≤ 2^k`, `q² / 2^(k + e) ≤ q · 2^-e`. -/
theorem sq_div_le_mul_inv_pow {q k : ℕ} (e : ℕ) (hq : q ≤ 2 ^ k) :
    (q : ℝ≥0∞) ^ 2 / 2 ^ (k + e) ≤ (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ e := by
  have hq' : (q : ℝ≥0∞) ≤ 2 ^ k := by exact_mod_cast hq
  have h2k : (2 : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2k' : (2 : ℝ≥0∞) ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc (q : ℝ≥0∞) ^ 2 / 2 ^ (k + e) ≤ (q : ℝ≥0∞) * 2 ^ k / (2 ^ e * 2 ^ k) := by
        rw [pow_two, pow_add, mul_comm ((2 : ℝ≥0∞) ^ k) ((2 : ℝ≥0∞) ^ e)]
        gcongr
    _ = (q : ℝ≥0∞) / 2 ^ e := ENNReal.mul_div_mul_right _ _ h2k h2k'
    _ = (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ e := by rw [div_eq_mul_inv, ENNReal.inv_pow]

end Common
