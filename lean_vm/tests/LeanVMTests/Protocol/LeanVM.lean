import LeanVM.Protocol.LeanVM

/-!
# The leanVM front page, locked: completeness

Statement locks of `LeanVM/Protocol/LeanVM.lean`: completeness in the random-oracle model and
its numbers, with the axioms each depends on. Knowledge soundness is locked in
`LeanVMTests.Protocol.LeanVMSound`.
-/

open LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.LeanIsa LeanVM

example {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28) {ρ : ℕ}
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← experiment (honestProver prog input t ρ fuel)}[z.1.2 = false] ≤
      completenessError fuel :=
  completeness hv hbudget hρ hfuel

example : completenessError (2 ^ 25) ≤ (2 : ENNReal)⁻¹ ^ 128 := completenessError_le

/-- info: 'LeanVM.completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms completeness

/--
info: 'LeanVM.completenessError_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms completenessError_le

/-! ## The statements of `LeanVM/Spec/Statement.lean` -/

example : Completeness := completeness_holds

/--
info: 'LeanVM.completeness_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms completeness_holds
