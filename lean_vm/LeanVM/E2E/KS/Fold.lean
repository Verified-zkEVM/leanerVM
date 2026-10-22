import LeanVM.E2E.Unforgeable

/-!
# The signature bounds in one term

`signatureBounds_le`: leanXMSS's multi-user bound at `Q + 384` and leanSPHINCS's `n_s (Q + 686) /
2^127`, `Q` at least the key generations' work, are at most `(n_s + n_x/2^23 + 4) · q / 2^127` for
every `q ≥ Q` below the trivial range. They are two of the terms `noForgery_core_le` bounds, and
`unforgeable_le` folds its quadratic term.
-/

namespace LeanVM.E2E.KS

open LeanVM.E2E
open scoped ENNReal

/-- **The signature bounds in one term.** -/
theorem signatureBounds_le {nx ns Q q : ℕ} (hQ : nx * 2 ^ 23 + ns * 2 ^ 15 ≤ Q) (hQq : Q ≤ q)
    (hl : q * (2 ^ 129 * ns + 2 ^ 106 * nx + 2 ^ 131) < 2 ^ 256) :
    (if nx = 0 then 0 else xmssMultiError nx (Q + 384)) +
        (ns : ℝ≥0∞) * (((Q + 686 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞)) ≤
      ((ns : ℝ≥0∞) + nx / 2 ^ 23 + 4) * q / 2 ^ 127 := by
  calc (if nx = 0 then 0 else xmssMultiError nx (Q + 384)) +
        (ns : ℝ≥0∞) * (((Q + 686 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞))
      ≤ (chainCoreNum Q : ℝ≥0∞) / 2 ^ 256 + (if nx = 0 then 0 else xmssMultiError nx (Q + 384)) +
          (ns : ℝ≥0∞) * (((Q + 686 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞)) := by
        rw [add_assoc]; exact le_add_self
    _ ≤ Q * noForgeryRate nx ns + ((29 * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := noForgery_core_le hQ
    _ ≤ q * noForgeryRate nx ns + ((30 * q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
        add_le_add (mul_le_mul_left (Nat.cast_le.mpr hQq) _) (ENNReal.div_le_div_right
          (Nat.cast_le.mpr (Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hQq 2))) _)
    _ ≤ ((ns : ℝ≥0∞) + nx / 2 ^ 23 + 4) * q / 2 ^ 127 := unforgeable_le hl

end LeanVM.E2E.KS
