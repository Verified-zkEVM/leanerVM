import LeanVM.Protocol.LeanVMRpm

/-!
# leanVM's statements, locked

Statement locks of `LeanVM/Protocol/LeanVMRpm.lean`: knowledge soundness and completeness in the
random-permutation model (`Statement/LeanVm.lean`), the statements of the specification, and their
numbers, with the axioms each depends on.
-/

open LeanVM.Semantics LeanVM

example {A : RpmAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← rpmExperiment A}[z.1.2 = true ∧
      ¬ ∃ t, extractorRpm z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2 = some t ∧
        ValidExecution z.1.1.1.1 z.1.1.1.2 t] ≤
      soundnessError Q + rpmError (Q + verifierPermCalls) :=
  knowledgeSoundness_holds A Q hA

/-- The numbers: `12008 · 2^32` permutation calls of the verifier, `q² / 2^508`. -/
example (q : ℕ) : rpmError q = (q ^ 2 : ENNReal) / 2 ^ 508 := rfl

example : verifierPermCalls = 12008 * 2 ^ 32 := rfl

example {A : RpmAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) (hQ : Q ≤ 2 ^ 120) :
    Pr{let z ← rpmExperiment A}[BreaksRpm extractorRpm z] ≤
      (Q + 2 ^ 14 : ENNReal) * (2 : ENNReal)⁻¹ ^ 127 :=
  knowledgeSoundness_bits A Q hA hQ

example : KnowledgeSoundness := knowledgeSoundness_holds

example : Completeness := completeness_holds

/--
info: 'LeanVM.knowledgeSoundness_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms knowledgeSoundness_holds

/--
info: 'LeanVM.knowledgeSoundness_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms knowledgeSoundness_bits

/--
info: 'LeanVM.completeness_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms completeness_holds
