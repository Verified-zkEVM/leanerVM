/-
  LeanVM.E2E.Vis.Closed2

  The end theorem's error with T3 from two challenges, `sec0Error2`, and its numerics.
-/

module

public import LeanVM.E2E.Vis.Bound2
public import LeanVM.E2E.Vis.Closed

/-!
# §0's bound with T3 from two challenges (W-vis)

**Internal** (decision E2E-12): superseded as an end theorem by `LeanVM/E2E/Main.lean`, which
states the whole result. Kept as proved; its axiom pins are in `tests/LeanVMTests/E2E/Pins.lean`.

Pure arithmetic. `sec0Error2` is `sec0Error` (`Vis/Closed.lean`) with the chain's error
`visError2` (`Vis/Bound2.lean`): T3's term is `Q_v³ / (6 · 2^384)` (`predError2`) instead of
`Q_v (Q_v + 1) / 2^193`, every other term unchanged (`sec0Error2_add`).

**As a fraction.** T3's new term is no integer over `2^256`, so `sec0Num2` (the numerator over
`2^256`) carries it rounded up, `⌊Q_v³ / (6 · 2^128)⌋ + 1`, and `sec0Error2 ≤ sec0Num2 / 2^256`
(`sec0Error2_le_num`).

**Numerics** (the points of `Vis/Closed.lean`; the T3 term is below `2^-194` there, against the
old `2^-65`, so the points' values change only in the 8th decimal of their exponents):

| point | `sec0Error2` |
| --- | --- |
| lifetime: `n_x = n_s = 2^20`, `Q_v ≤ 2^64`, `s_X, s_S ≤ 2^44`, `s_Xk, s_Sk ≤ 2^24` | `≤ 2^-41` (`≈ 2^-41.97`) |
| one slot: `s_X, s_S, s_Xk, s_Sk ≤ 2^20` | `≤ 2^-42 + 2^-51` |
| leanXMSS only, lifetime, `Q_v ≤ 2^64` | `≤ 2^-42` (`≈ 2^-42.99`) |
| leanXMSS only, lifetime, `Q_v ≤ 2^56` | `≤ 2^-49` (`≈ 2^-49.41`) |

What changes is the shape in `Q_v`: the T3 term is below `Q_v² / 2^256` for `Q_v ≤ 2^128`
(`predError2_le_sq`), so no term of `sec0Error2` is a birthday bound over fewer than 256 bits.
-/

namespace LeanVM.E2E

open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.EndToEnd.Sound
open scoped ENNReal

@[expose] public section

/-! ## The proofs' bound -/

/-- **§0's bound with the constants the proofs give, T3 from two challenges.** -/
noncomputable def sec0Error2 (Qv Q nx ns qx qs Qk : ℕ) : ℝ≥0∞ :=
  visError2 Qv Q (nx + ns) + perKeyError Qv nx ns qx qs Qk

/-- **`sec0Error2` at the end theorem's arguments** (as `sec0ErrorGame`). -/
noncomputable def sec0ErrorGame2 (nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk : ℕ) :
    ℝ≥0∞ :=
  sec0Error2 (qH + budget) (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget) nx ns
    (2 * (nx + ns) + cxk + sXk * cxs + cx) (2 * (nx + ns) + csk + sSk * css + cs)
    (nx * cxk + ns * csk)

/-- **Against the old bound**: `sec0Error2` is `sec0Error` with `Q_v³ / (6 · 2^384)` for
`Q_v (Q_v + 1) / 2^193`. -/
theorem sec0Error2_add (Qv Q nx ns qx qs Qk : ℕ) :
    sec0Error2 Qv Q nx ns qx qs Qk + Qv * (Qv + 1) / 2 ^ 193 =
      sec0Error Qv Q nx ns qx qs Qk + predError2 Qv := by
  rw [sec0Error2, sec0Error, add_right_comm, visError2_add, add_right_comm]

/-! ## As a fraction over `2^256` -/

/-- `sec0Error2 Qv Q nx ns qx qs Qk`, times `2^256`, T3's term rounded up. -/
def sec0Num2 (Qv Q nx ns qx qs Qk : ℕ) : ℕ :=
  2 ^ 128 * Qv + 2 ^ 65 * Qv + 14 * 2 ^ 64 * Q + (Qv ^ 3 / (6 * 2 ^ 128) + 1) +
    Q * (5 * (Q + 1) + 4 * (Q + 2) + 4 * (Q + 1) + ((nx + ns) * 2 ^ 64 + 1)) +
    2 ^ 129 * (nx * (Qv + qx)) + 2 ^ 129 * (ns * (Qv + qs)) +
    (nx + ns) * (2 ^ 129 * (nx + ns) + Qk ^ 2)

/-- **`sec0Error2` is at most one fraction.** -/
theorem sec0Error2_le_num (Qv Q nx ns qx qs Qk : ℕ) :
    sec0Error2 Qv Q nx ns qx qs Qk ≤ (sec0Num2 Qv Q nx ns qx qs Qk : ℝ≥0∞) / 2 ^ 256 := by
  set I := ((2 : ℝ≥0∞) ^ 256)⁻¹
  have h128 : ((2 : ℝ≥0∞) ^ 128)⁻¹ = 2 ^ 128 * I := inv_two_pow_eq 128 (by norm_num)
  have h192 : ((2 : ℝ≥0∞) ^ 192)⁻¹ = 2 ^ 64 * I := inv_two_pow_eq 192 (by norm_num)
  have h127 : ((2 : ℝ≥0∞) ^ 127)⁻¹ = 2 ^ 129 * I := inv_two_pow_eq 127 (by norm_num)
  have hs : (4 + leanVmSeeds.steps.length) * (Q + 1) = 5 * (Q + 1) := rfl
  have hT := predError2_le_num Qv
  set T := predError2 Qv
  have e : sec0Error2 Qv Q nx ns qx qs Qk =
      T + (((sec0Num2 Qv Q nx ns qx qs Qk - (Qv ^ 3 / (6 * 2 ^ 128) + 1) : ℕ) : ℝ≥0∞) /
        2 ^ 256) := by
    have hle : Qv ^ 3 / (6 * 2 ^ 128) + 1 ≤ sec0Num2 Qv Q nx ns qx qs Qk := by
      unfold sec0Num2; omega
    have hc : sec0Num2 Qv Q nx ns qx qs Qk - (Qv ^ 3 / (6 * 2 ^ 128) + 1) =
        2 ^ 128 * Qv + 2 ^ 65 * Qv + 14 * 2 ^ 64 * Q +
          Q * (5 * (Q + 1) + 4 * (Q + 2) + 4 * (Q + 1) + ((nx + ns) * 2 ^ 64 + 1)) +
          2 ^ 129 * (nx * (Qv + qx)) + 2 ^ 129 * (ns * (Qv + qs)) +
          (nx + ns) * (2 ^ 129 * (nx + ns) + Qk ^ 2) := by
      unfold sec0Num2; omega
    rw [hc]
    simp only [sec0Error2, visError2, perKeyError, εLean, failBound, hs, div_eq_mul_inv,
      ← ENNReal.inv_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      h128, h192, h127]
    ring
  have hsplit : (sec0Num2 Qv Q nx ns qx qs Qk : ℝ≥0∞) / 2 ^ 256 =
      ((Qv ^ 3 / (6 * 2 ^ 128) + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        ((sec0Num2 Qv Q nx ns qx qs Qk - (Qv ^ 3 / (6 * 2 ^ 128) + 1) : ℕ) : ℝ≥0∞) /
          2 ^ 256 := by
    rw [ENNReal.div_add_div_same, ← Nat.cast_add, Nat.add_sub_cancel' (by unfold sec0Num2; omega)]
  rw [e, hsplit]
  exact add_le_add hT le_rfl

/-- `sec0Num2` grows with each argument. -/
theorem sec0Num2_mono {Qv Q nx ns qx qs Qk Qv' Q' nx' ns' qx' qs' Qk' : ℕ} (hv : Qv ≤ Qv')
    (hQ : Q ≤ Q') (hx : nx ≤ nx') (hs : ns ≤ ns') (hqx : qx ≤ qx') (hqs : qs ≤ qs')
    (hk : Qk ≤ Qk') :
    sec0Num2 Qv Q nx ns qx qs Qk ≤ sec0Num2 Qv' Q' nx' ns' qx' qs' Qk' := by
  have h3 : Qv ^ 3 / (6 * 2 ^ 128) ≤ Qv' ^ 3 / (6 * 2 ^ 128) :=
    Nat.div_le_div_right (Nat.pow_le_pow_left hv 3)
  unfold sec0Num2
  gcongr

/-! ## Numerics -/

/-- **The lifetime point**: `sec0Error2 ≤ 2^-42 + 2^-47` (about `2^-41.97`). -/
theorem sec0ErrorGame2_lifetime {csk css qH budget sX sS sXk sSk : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44) (hS : sS ≤ 2 ^ 44)
    (hXk : sXk ≤ 2 ^ 24) (hSk : sSk ≤ 2 ^ 24) :
    sec0ErrorGame2 (2 ^ 20) (2 ^ 20) 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk ≤
      (2 : ℝ≥0∞)⁻¹ ^ 42 + (2 : ℝ≥0∞)⁻¹ ^ 47 := by
  rw [sec0ErrorGame2, two_inv_pow_eq_div 42 (by norm_num), two_inv_pow_eq_div 47 (by norm_num),
    ENNReal.div_add_div_same, ← Nat.cast_add]
  refine (sec0Error2_le_num _ _ _ _ _ _ _).trans (div_two_pow_256_le
    ((sec0Num2_mono (by exact hQ) (gameQueries_vis_le hk hs hQ hX hS) le_rfl le_rfl
    (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hXk) _) _)
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hk _) (Nat.mul_le_mul hSk hs)) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hk) _)).trans ?_))
  unfold sec0Num2
  norm_num

/-- **The lifetime point, as asked**: `sec0Error2 ≤ 2^-41`. -/
theorem sec0ErrorGame2_lifetime_le {csk css qH budget sX sS sXk sSk : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44) (hS : sS ≤ 2 ^ 44)
    (hXk : sXk ≤ 2 ^ 24) (hSk : sSk ≤ 2 ^ 24) :
    sec0ErrorGame2 (2 ^ 20) (2 ^ 20) 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk ≤
      (2 : ℝ≥0∞)⁻¹ ^ 41 := by
  refine (sec0ErrorGame2_lifetime hk hs hQ hX hS hXk hSk).trans ?_
  rw [two_inv_pow_eq_div 42 (by norm_num), two_inv_pow_eq_div 47 (by norm_num),
    two_inv_pow_eq_div 41 (by norm_num), ENNReal.div_add_div_same, ← Nat.cast_add]
  exact div_two_pow_256_le (by norm_num)

/-- **One slot**: `sec0Error2 ≤ 2^-42 + 2^-51`. -/
theorem sec0ErrorGame2_one_slot {csk css qH budget sX sS sXk sSk : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 20) (hS : sS ≤ 2 ^ 20)
    (hXk : sXk ≤ 2 ^ 20) (hSk : sSk ≤ 2 ^ 20) :
    sec0ErrorGame2 (2 ^ 20) (2 ^ 20) 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk ≤
      (2 : ℝ≥0∞)⁻¹ ^ 42 + (2 : ℝ≥0∞)⁻¹ ^ 51 := by
  rw [sec0ErrorGame2, two_inv_pow_eq_div 42 (by norm_num), two_inv_pow_eq_div 51 (by norm_num),
    ENNReal.div_add_div_same, ← Nat.cast_add]
  refine (sec0Error2_le_num _ _ _ _ _ _ _).trans (div_two_pow_256_le
    ((sec0Num2_mono (by exact hQ) (gameQueries_vis_le hk hs hQ hX hS) le_rfl le_rfl
    (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hXk) _) _)
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hk _) (Nat.mul_le_mul hSk hs)) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hk) _)).trans ?_))
  unfold sec0Num2
  norm_num

/-- **leanXMSS only, lifetime**, `Q_v ≤ 2^64`: `sec0Error2 ≤ 2^-42`. -/
theorem sec0ErrorGame2_lifetime_xmss {csk css qH budget sX sS sXk sSk : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44) (hS : sS ≤ 2 ^ 44)
    (hXk : sXk ≤ 2 ^ 24) :
    sec0ErrorGame2 (2 ^ 20) 0 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk ≤
      (2 : ℝ≥0∞)⁻¹ ^ 42 := by
  rw [sec0ErrorGame2, two_inv_pow_eq_div 42 (by norm_num)]
  refine (sec0Error2_le_num _ _ _ _ _ _ _).trans (div_two_pow_256_le
    ((sec0Num2_mono (by exact hQ) (gameQueries_vis_le hk hs hQ hX hS) le_rfl le_rfl
    (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hXk) _) _)
    le_rfl le_rfl).trans ?_))
  unfold sec0Num2
  norm_num

/-- **leanXMSS only, lifetime, `Q_v ≤ 2^56`**: `sec0Error2 ≤ 2^-49`. -/
theorem sec0ErrorGame2_lifetime_xmss_56 {csk css qH budget sX sS sXk sSk : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 56) (hX : sX ≤ 2 ^ 44) (hS : sS ≤ 2 ^ 44)
    (hXk : sXk ≤ 2 ^ 24) :
    sec0ErrorGame2 (2 ^ 20) 0 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk ≤
      (2 : ℝ≥0∞)⁻¹ ^ 49 := by
  rw [sec0ErrorGame2, two_inv_pow_eq_div 49 (by norm_num)]
  refine (sec0Error2_le_num _ _ _ _ _ _ _).trans (div_two_pow_256_le
    ((sec0Num2_mono (by exact hQ)
    (gameQueries_vis_le hk hs (hQ.trans (by norm_num)) hX hS)
    le_rfl le_rfl (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hXk) _) _)
    le_rfl le_rfl).trans ?_))
  unfold sec0Num2
  norm_num

end
end LeanVM.E2E
