import LeanVM.E2E.Vis.Closed

/-!
# Tests: W-vis P6b, the closed forms and their numerics

`LeanVM.E2E.Vis.Closed`: `sec0Error` (the proofs' bound), `eps0` (§0's bound, literally) and
`delta` (their deviations), with `sec0Error ≤ eps0 + delta`, each as one fraction over `2^256`,
and their values at the lifetime, one-slot and leanXMSS-only points. The examples instantiate the
numerics at the `full` and `pruned20` constants and compare with today's `closedError` at the same
points; the pins check that the theorems rest on Lean's three standard axioms only.
-/

open LeanVM.E2E
open scoped ENNReal

/-- `sec0Error` is the chain's error plus the per-key terms. -/
example (Qv Q nx ns qx qs Qk : ℕ) :
    sec0Error Qv Q nx ns qx qs Qk = visError Qv Q (nx + ns) + perKeyError Qv nx ns qx qs Qk := rfl

/-- `delta` is the six named deviations. -/
example (Qv Q nx ns Qk : ℕ) :
    delta Qv Q nx ns Qk = deltaHidFail Qv Q + deltaDaVis Qv + deltaDaHid Qv Q +
      deltaFormat Q (nx + ns) + deltaFwd (nx + ns) + deltaKeyColl (nx + ns) Qk := rfl

/-- With no query and no key, every deviation vanishes. -/
example : delta 0 0 0 0 0 = 0 := by
  rw [delta_eq_num]
  simp [deltaNum]

/-- The comparison at the end theorem's arguments, for every constant. -/
example (nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk : ℕ) :
    sec0ErrorGame nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk ≤
      eps0Game nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk +
        deltaGame nx ns cxk csk cxs css qH budget sX sS :=
  sec0ErrorGame_le ..

/-- **Lifetime, `full`** (`c_sk = 15,166,603,265`, `c_ss = 23,756,655,991`): `≤ 2^-41`. -/
example {qH budget sX sS sXk sSk : ℕ} (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44)
    (hS : sS ≤ 2 ^ 44) (hXk : sXk ≤ 2 ^ 24) (hSk : sSk ≤ 2 ^ 24) :
    sec0ErrorGame (2 ^ 20) (2 ^ 20) 13434881 15166603265 8630239197 23756655991 384 686 qH budget
      sX sS sXk sSk ≤ (2 : ℝ≥0∞)⁻¹ ^ 41 :=
  sec0ErrorGame_lifetime_le (by norm_num) (by norm_num) hQ hX hS hXk hSk

/-- **Lifetime, `pruned20`** (`c_sk = 236,978,189`, `c_ss = 8,827,030,915`): `≤ 2^-41`. -/
example {qH budget sX sS sXk sSk : ℕ} (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44)
    (hS : sS ≤ 2 ^ 44) (hXk : sXk ≤ 2 ^ 24) (hSk : sSk ≤ 2 ^ 24) :
    sec0ErrorGame (2 ^ 20) (2 ^ 20) 13434881 236978189 8630239197 8827030915 384 686 qH budget
      sX sS sXk sSk ≤ (2 : ℝ≥0∞)⁻¹ ^ 41 :=
  sec0ErrorGame_lifetime_le (by norm_num) (by norm_num) hQ hX hS hXk hSk

/-- **The deviations at the lifetime, `full`**: `≤ 2^-83`. -/
example {qH budget sX sS : ℕ} (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44) (hS : sS ≤ 2 ^ 44) :
    deltaGame (2 ^ 20) (2 ^ 20) 13434881 15166603265 8630239197 23756655991 qH budget sX sS ≤
      (2 : ℝ≥0∞)⁻¹ ^ 83 :=
  deltaGame_lifetime_le (by norm_num) (by norm_num) hQ hX hS

/-- **`delta ≤ 2^-84` fails at the lifetime point**: at `qH + budget = 2^64` and `2^44` requests
per scheme the deviations are at least `2^-84 + 2^-86`. -/
example : (2 : ℝ≥0∞)⁻¹ ^ 84 + (2 : ℝ≥0∞)⁻¹ ^ 86 ≤
    deltaGame (2 ^ 20) (2 ^ 20) 13434881 15166603265 8630239197 23756655991 (2 ^ 64) 0
      (2 ^ 44) (2 ^ 44) := by
  rw [deltaGame, delta_eq_num, two_inv_pow_eq_div 84 (by norm_num),
    two_inv_pow_eq_div 86 (by norm_num), ENNReal.div_add_div_same, ← Nat.cast_add]
  exact div_two_pow_256_le (by norm_num [deltaNum])

/-- **One slot, `full`**: `≤ 2^-42 + 2^-51`. -/
example {qH budget sX sS sXk sSk : ℕ} (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 20)
    (hS : sS ≤ 2 ^ 20) (hXk : sXk ≤ 2 ^ 20) (hSk : sSk ≤ 2 ^ 20) :
    sec0ErrorGame (2 ^ 20) (2 ^ 20) 13434881 15166603265 8630239197 23756655991 384 686 qH budget
      sX sS sXk sSk ≤ (2 : ℝ≥0∞)⁻¹ ^ 42 + (2 : ℝ≥0∞)⁻¹ ^ 51 :=
  sec0ErrorGame_one_slot (by norm_num) (by norm_num) hQ hX hS hXk hSk

/-- **One slot is above `2^-42`** at `qH + budget = 2^64` and `2^20` requests to each key. -/
example : (2 : ℝ≥0∞)⁻¹ ^ 42 ≤
    sec0ErrorGame (2 ^ 20) (2 ^ 20) 13434881 15166603265 8630239197 23756655991 384 686 (2 ^ 64) 0
      (2 ^ 20) (2 ^ 20) (2 ^ 20) (2 ^ 20) := by
  rw [sec0ErrorGame, sec0Error_eq_num, two_inv_pow_eq_div 42 (by norm_num)]
  exact div_two_pow_256_le (by norm_num [closedNum0])

/-- **leanXMSS only, lifetime**: `≤ 2^-42` at `Q_v ≤ 2^64`, `≤ 2^-49` at `Q_v ≤ 2^56`. -/
example {qH budget sX sXk : ℕ} (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44)
    (hXk : sXk ≤ 2 ^ 24) :
    sec0ErrorGame (2 ^ 20) 0 13434881 15166603265 8630239197 23756655991 384 686 qH budget sX 0
      sXk 0 ≤ (2 : ℝ≥0∞)⁻¹ ^ 42 :=
  sec0ErrorGame_lifetime_xmss (by norm_num) (by norm_num) hQ hX (by norm_num) hXk

example {qH budget sX sXk : ℕ} (hQ : qH + budget ≤ 2 ^ 56) (hX : sX ≤ 2 ^ 44)
    (hXk : sXk ≤ 2 ^ 24) :
    sec0ErrorGame (2 ^ 20) 0 13434881 15166603265 8630239197 23756655991 384 686 qH budget sX 0
      sXk 0 ≤ (2 : ℝ≥0∞)⁻¹ ^ 49 :=
  sec0ErrorGame_lifetime_xmss_56 (by norm_num) (by norm_num) hQ hX (by norm_num) hXk

/-! ### Today's `closedError` at the same points (`full`, `qH + budget = 2^64`) -/

/-- Lifetime: today's bound is above `2^-29` (about `2^-28.07`). -/
example : (2 : ℝ≥0∞)⁻¹ ^ 29 ≤
    closedError (2 ^ 20 * 13434881 + 2 ^ 20 * 15166603265 +
      (2 ^ 64 + 2 ^ 44 * 8630239197 + 2 ^ 44 * 23756655991) + 0) (2 ^ 20) (2 ^ 20) := by
  rw [closedError_eq_num, two_inv_pow_eq_div 29 (by norm_num)]
  exact div_two_pow_256_le (by norm_num [closedNum])

/-- One slot: today's bound is between `2^-43` and `2^-43 + 2^-51` (about `2^-43.0`). -/
example : (2 : ℝ≥0∞)⁻¹ ^ 43 ≤
    closedError (2 ^ 20 * 13434881 + 2 ^ 20 * 15166603265 +
      (2 ^ 64 + 2 ^ 20 * 8630239197 + 2 ^ 20 * 23756655991) + 0) (2 ^ 20) (2 ^ 20) := by
  rw [closedError_eq_num, two_inv_pow_eq_div 43 (by norm_num)]
  exact div_two_pow_256_le (by norm_num [closedNum])

example : closedError (2 ^ 20 * 13434881 + 2 ^ 20 * 15166603265 +
      (2 ^ 64 + 2 ^ 20 * 8630239197 + 2 ^ 20 * 23756655991) + 0) (2 ^ 20) (2 ^ 20) ≤
    (2 : ℝ≥0∞)⁻¹ ^ 43 + (2 : ℝ≥0∞)⁻¹ ^ 51 := by
  rw [closedError_eq_num, two_inv_pow_eq_div 43 (by norm_num), two_inv_pow_eq_div 51 (by norm_num),
    ENNReal.div_add_div_same, ← Nat.cast_add]
  exact div_two_pow_256_le (by norm_num [closedNum])

/-- leanXMSS only, lifetime: today's bound is above `2^-40` (about `2^-38.99`). -/
example : (2 : ℝ≥0∞)⁻¹ ^ 40 ≤
    closedError (2 ^ 20 * 13434881 + 0 * 15166603265 + (2 ^ 64 + 2 ^ 44 * 8630239197 + 0) + 0)
      (2 ^ 20) 0 := by
  rw [closedError_eq_num, two_inv_pow_eq_div 40 (by norm_num)]
  exact div_two_pow_256_le (by norm_num [closedNum])

/-! ### Axioms -/

/-- info: 'LeanVM.E2E.sec0Error_eq_num' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sec0Error_eq_num

/-- info: 'LeanVM.E2E.eps0_eq_num' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.eps0_eq_num

/-- info: 'LeanVM.E2E.delta_eq_num' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.delta_eq_num

/-- info: 'LeanVM.E2E.closedNum0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.closedNum0_le

/-- info: 'LeanVM.E2E.sec0Error_le_eps0_add_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sec0Error_le_eps0_add_delta

/-- info: 'LeanVM.E2E.sec0ErrorGame_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sec0ErrorGame_le

/-- info: 'LeanVM.E2E.deltaFwd_lifetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.deltaFwd_lifetime

/-- info: 'LeanVM.E2E.sec0ErrorGame_lifetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sec0ErrorGame_lifetime

/-- info: 'LeanVM.E2E.sec0ErrorGame_lifetime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sec0ErrorGame_lifetime_le

/-- info: 'LeanVM.E2E.deltaGame_lifetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.deltaGame_lifetime

/-- info: 'LeanVM.E2E.deltaGame_lifetime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.deltaGame_lifetime_le

/-- info: 'LeanVM.E2E.sec0ErrorGame_one_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sec0ErrorGame_one_slot

/-- info: 'LeanVM.E2E.sec0ErrorGame_lifetime_xmss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sec0ErrorGame_lifetime_xmss

/-- info: 'LeanVM.E2E.sec0ErrorGame_lifetime_xmss_56' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sec0ErrorGame_lifetime_xmss_56
