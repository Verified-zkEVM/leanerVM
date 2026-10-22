import LeanVM.E2E.Headline

/-!
# Tests: the headline

* `aggregate_no_forgery_final` and its corollaries rest on Lean's three axioms.
* Every proved leanSPHINCS parameter set has its `SphincsSet` instance, and the headline applies
  at each (instance resolution from the parameter set alone).
* `q` at the proved costs, at `full`, and V_I's budget `viCost N = N · 2^40`.
* The rates: `λ₁ = 106` at `2^20 + 2^20` keys, `126` with leanXMSS keys only, and the exact
  numerator.
* **One slot** at `full` (`qH + viCost N ≤ 2^64`, `2^20` requests per scheme): at most `2^-42`.
-/

namespace LeanVMTests.E2E.Headline

open OracleComp OracleSpec LeanVM LeanVM.E2E
open scoped ENNReal

/-! ## Axioms -/

/-- info: 'LeanVM.E2E.aggregate_no_forgery_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_final

/-- info: 'LeanVM.E2E.aggregate_no_forgery_final_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_final_deployed

/-- info: 'LeanVM.E2E.aggregate_no_forgery_final_xmss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_final_xmss

/-- info: 'LeanVM.E2E.aggregate_no_forgery_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_linear

/-! ## The parameter sets -/

example : SphincsSet Sphincs.Lifetimes.full := inferInstance
example : SphincsSet Sphincs.Lifetimes.pruned20 := inferInstance
example : SphincsSet Sphincs.Lifetimes.pruned14 := inferInstance
example : SphincsSet Sphincs.Lifetimes.pruned13 := inferInstance
example : SphincsSet Sphincs.Lifetimes.pruned12 := inferInstance
example : SphincsSet Sphincs.Lifetimes.pruned10 := inferInstance
example : SphincsSet Sphincs.Lifetimes.pruned8 := inferInstance

section Pruned12

attribute [local instance] Sphincs.Lifetimes.pruned12

/-- The headline at the Rust test signers' set: `SphincsSet` found from the parameter set. -/
example {nx ns : ℕ} (N : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[E2E.Breaks z.1 z.2] ≤
      (totalQueries nx ns qH sX sS N : ℝ≥0∞) * noForgeryRate nx ns +
        ((30 * totalQueries nx ns qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  aggregate_no_forgery_final N A hA

end Pruned12

/-! ## `q` -/

example (nx ns qH sX sS N : ℕ) :
    @totalQueries Sphincs.Lifetimes.full nx ns qH sX sS N =
      nx * 13434881 + ns * 15166603265 + qH + sX * 8630239197 + sS * 23756655991 +
        N * 2 ^ 40 := by
  rw [@totalQueries_eq Sphincs.Lifetimes.full sphincsSetFull]
  rfl

/-! ## The rates -/

example : noForgeryRateNum (2 ^ 20) (2 ^ 20) = 2 ^ 128 * (3 + 2 ^ 21) + 2 ^ 124 + 2 ^ 126 := by
  norm_num [noForgeryRateNum]

example : noForgeryRate (2 ^ 20) (2 ^ 20) ≤ (2 : ℝ≥0∞)⁻¹ ^ 106 := noForgeryRate_deployed

example : noForgeryRate (2 ^ 21) 0 ≤ (2 : ℝ≥0∞)⁻¹ ^ 126 := noForgeryRate_xmss_only le_rfl

/-! ## One slot -/

/-- At `full`, `2^20 + 2^20` keys, `qH + viCost N ≤ 2^64` and `2^20` requests per scheme, the
headline's bound is at most `2^-42` (about `2^-43.0`). -/
theorem one_slot_full_le {qH sX sS N : ℕ} (hQ : qH + viCost N ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 20)
    (hS : sS ≤ 2 ^ 20) :
    (@totalQueries Sphincs.Lifetimes.full (2 ^ 20) (2 ^ 20) qH sX sS N : ℝ≥0∞) *
        noForgeryRate (2 ^ 20) (2 ^ 20) +
      ((30 * @totalQueries Sphincs.Lifetimes.full (2 ^ 20) (2 ^ 20) qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) /
        2 ^ 256 ≤ (2 : ℝ≥0∞)⁻¹ ^ 42 := by
  set q := @totalQueries Sphincs.Lifetimes.full (2 ^ 20) (2 ^ 20) qH sX sS N
  have hq : q ≤ 2 ^ 64 + 2 ^ 20 * (13434881 + 15166603265 + 8630239197 + 23756655991) := by
    have e : q = 2 ^ 20 * 13434881 + 2 ^ 20 * 15166603265 + qH + sX * 8630239197 +
        sS * 23756655991 + viCost N :=
      @totalQueries_eq Sphincs.Lifetimes.full sphincsSetFull (2 ^ 20) (2 ^ 20) qH sX sS N
    have h1 : sX * 8630239197 ≤ 2 ^ 20 * 8630239197 := Nat.mul_le_mul_right _ hX
    have h2 : sS * 23756655991 ≤ 2 ^ 20 * 23756655991 := Nat.mul_le_mul_right _ hS
    rw [e]
    linarith
  have e : (q : ℝ≥0∞) * noForgeryRate (2 ^ 20) (2 ^ 20) + ((30 * q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 =
      ((q * noForgeryRateNum (2 ^ 20) (2 ^ 20) + 30 * q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    simp only [noForgeryRate, Nat.cast_add, Nat.cast_mul, ENNReal.add_div, mul_div_assoc]
  rw [e, ← ENNReal.inv_pow, inv_two_pow_eq 42 (by norm_num), div_eq_mul_inv]
  gcongr
  have hn : q * noForgeryRateNum (2 ^ 20) (2 ^ 20) + 30 * q ^ 2 ≤ 2 ^ (256 - 42) :=
    calc q * noForgeryRateNum (2 ^ 20) (2 ^ 20) + 30 * q ^ 2
        ≤ (2 ^ 64 + 2 ^ 20 * (13434881 + 15166603265 + 8630239197 + 23756655991)) *
            noForgeryRateNum (2 ^ 20) (2 ^ 20) +
          30 * (2 ^ 64 + 2 ^ 20 * (13434881 + 15166603265 + 8630239197 + 23756655991)) ^ 2 := by
          gcongr
      _ ≤ 2 ^ (256 - 42) := by norm_num [noForgeryRateNum]
  exact_mod_cast hn

end LeanVMTests.E2E.Headline
