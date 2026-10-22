import LeanVM.E2E.HeadlineSharp

/-!
# Tests: the sharp headline

* `aggregate_no_forgery_final_sharp`, its deployed form and the per-set evaluations rest on Lean's
  three axioms (the certificates' constants by `decide +kernel`).
* Every proved leanSPHINCS parameter set has its `SphincsSetSharp` instance.
* At `full` and `pruned20`, `2^20 + 2^20` keys: `Pr[Breaks] ≤ q · 2^-116 + 2^34 q²/2^256`.
* The constants: `β = linB/2^128 ≈ 0.0020` at `full`, `0.0036` at `pruned20`; `D = 10,857` at `full`
  (`2^13.41`, set by the certificate's budget), against the per-key `4(1 + Cq) = 1,348`.
-/

namespace LeanVMTests.E2E.HeadlineSharp

open OracleComp OracleSpec LeanVM LeanVM.E2E
open scoped ENNReal

/-! ## Axioms -/

/-- info: 'LeanVM.E2E.aggregate_no_forgery_final_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_final_sharp

/-- info: 'LeanVM.E2E.aggregate_no_forgery_final_sharp_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_final_sharp_deployed

/-- info: 'LeanVM.E2E.sharp_full_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sharp_full_deployed

/-- info: 'LeanVM.E2E.sharp_pruned20_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sharp_pruned20_deployed

/-- info: 'LeanVM.E2E.sphincsSetSharpPruned8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincsSetSharpPruned8

/-! ## The parameter sets -/

noncomputable example : SphincsSetSharp Sphincs.Lifetimes.full := inferInstance
noncomputable example : SphincsSetSharp Sphincs.Lifetimes.pruned20 := inferInstance
noncomputable example : SphincsSetSharp Sphincs.Lifetimes.pruned14 := inferInstance
noncomputable example : SphincsSetSharp Sphincs.Lifetimes.pruned13 := inferInstance
noncomputable example : SphincsSetSharp Sphincs.Lifetimes.pruned12 := inferInstance
noncomputable example : SphincsSetSharp Sphincs.Lifetimes.pruned10 := inferInstance
noncomputable example : SphincsSetSharp Sphincs.Lifetimes.pruned8 := inferInstance

/-! ## The deployed sets -/

section Full

attribute [local instance] Sphincs.Lifetimes.full

/-- `full`, `2^20 + 2^20` keys: `q · 2^-116 + 2^34 q²/2^256`. -/
example (N : ℕ) (A : GameAdversary (2 ^ 20) (2 ^ 20)) {qH sX sS : ℕ}
    (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[E2E.Breaks z.1 z.2] ≤
      (totalQueries (2 ^ 20) (2 ^ 20) qH sX sS N : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 116 +
        ((2 ^ 34 * totalQueries (2 ^ 20) (2 ^ 20) qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  aggregate_no_forgery_final_sharp_deployed sharp_full_deployed N A hA

/-- `β ≤ 1/500` per key per query, `ρ' ≤ 1.76` free of `n_s`, `D = 10,857`. -/
example : 500 * SphincsSetSharp.linB Sphincs.Lifetimes.full ≤ 2 ^ 128 ∧
    100 * SphincsSetSharp.linA Sphincs.Lifetimes.full ≤ 176 * 2 ^ 128 ∧
    SphincsSetSharp.quadD Sphincs.Lifetimes.full = 10857 := by
  decide

end Full

section Pruned20

attribute [local instance] Sphincs.Lifetimes.pruned20

/-- `pruned20`, `2^20 + 2^20` keys: `q · 2^-116 + 2^34 q²/2^256`. -/
example (N : ℕ) (A : GameAdversary (2 ^ 20) (2 ^ 20)) {qH sX sS : ℕ}
    (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[E2E.Breaks z.1 z.2] ≤
      (totalQueries (2 ^ 20) (2 ^ 20) qH sX sS N : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 116 +
        ((2 ^ 34 * totalQueries (2 ^ 20) (2 ^ 20) qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  aggregate_no_forgery_final_sharp_deployed sharp_pruned20_deployed N A hA

/-- `β ≤ 1/270` per key per query. -/
example : 270 * SphincsSetSharp.linB Sphincs.Lifetimes.pruned20 ≤ 2 ^ 128 := by decide

end Pruned20

/-! ## Pruned sets -/

section Pruned8

attribute [local instance] Sphincs.Lifetimes.pruned8

/-- `pruned8`, `2^20 + 2^20` keys: `λ₁ = 114`. -/
example : noForgeryRateSharp (2 ^ 20) (2 ^ 20) ≤ (2 : ℝ≥0∞)⁻¹ ^ 114 :=
  noForgeryRateSharp_le_of (by norm_num) (by decide)

end Pruned8

end LeanVMTests.E2E.HeadlineSharp
