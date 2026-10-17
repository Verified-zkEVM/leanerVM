import XmssSecurity.Proof.Deterministic.TableToReference
import XmssSecurity.Proof.Seeded.GameComparison

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

attribute [local irreducible] gameAfterSecrets

theorem evalDist_parameter_continuation {α : Type} (next : PublicParameter → ProbComp α) :
    (do let output ← ($ᵗ HashOutput : ProbComp HashOutput); next (truncateHash output)) =ᵈ (do let parameter ← Concrete.samplePublicParameter; next parameter) := by
  have h := Rom.evalDist_truncate_uniformHashOutput.trans evalDist_samplePublicParameter.symm
  exact (EvalDistEq.of_eq (bind_map_left truncateHash _ next).symm).trans (h.bind_left next)


theorem evalDist_secrets_continuation {α : Type} (next : ChainSecrets → ProbComp α) :
    (do let outputs ← ($ᵗ ChainOutputs); next (outputSecrets outputs)) =ᵈ (do let secret ← Concrete.sampleSecret; next secret) := by
  refine EvalDistEq.trans ?_ (evalDist_sampleSecret.symm.bind_left next)
  refine (evalDist_chainOutputs_from_halves.bind_left _).trans ?_
  simp only [bind_assoc, pure_bind, outputSecrets_from_halves]
  apply EvalDistEq.bind_right
  intro secret
  exact OracleComp.EvalDistEq.bind_const _ _

theorem evalDist_referenceOutputs (adversary : Adversary) :
    (do
      let parameterOutput ← ($ᵗ HashOutput : ProbComp HashOutput)
      let outputs ← ($ᵗ ChainOutputs)
      (simulateQ romImpl (gameAfterSecrets adversary (truncateHash parameterOutput)
        (outputSecrets outputs))).run' ∅) =ᵈ ((simulateQ romImpl (gameCore Concrete.scheme adversary)).run' ∅) := by
  rw [gameCore_independent_eq, run'_lift_sample_bind]
  refine EvalDistEq.trans (my := (do
    let parameter ← Concrete.samplePublicParameter
    let outputs ← ($ᵗ ChainOutputs)
    (simulateQ romImpl (gameAfterSecrets adversary parameter (outputSecrets outputs))).run' ∅ :
      ProbComp _)) ?_ ?_
  · exact evalDist_parameter_continuation fun parameter => do
      let outputs ← ($ᵗ ChainOutputs)
      (simulateQ romImpl (gameAfterSecrets adversary parameter (outputSecrets outputs))).run' ∅
  apply EvalDistEq.bind_right
  intro parameter
  rw [run'_lift_sample_bind]
  exact evalDist_secrets_continuation fun secret =>
    (simulateQ romImpl (gameAfterSecrets adversary parameter secret)).run' ∅

theorem worldHandler_randomOracle : worldHandler randomOracle = romImpl := rfl

theorem evalDist_independentTableGame_memo (adversary : Adversary) :
    independentTableGame (memoAdversary adversary) =ᵈ ((simulateQ romImpl (gameCore Concrete.scheme (memoAdversary adversary))).run' ∅) := by
  refine EvalDistEq.trans ?_ (evalDist_referenceOutputs _)
  unfold independentTableGame drawSigningMaterial
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro parameterOutput
  apply EvalDistEq.bind_right
  intro outputs
  have h := evalDist_tableGameAfterSecrets_memo randomOracle adversary (truncateHash parameterOutput) (outputSecrets outputs) ∅
  rw [worldHandler_randomOracle] at h
  have heq := h.map Prod.fst
  simpa only [StateT.run'_eq, map_bind] using heq

theorem forgeAdvantage_deterministic_le_reference (adversary : Adversary) (q : Nat)
    (hbound : HasTableBudget adversary q) :
    forgeAdvantage scheme adversary ≤ forgeAdvantage Concrete.scheme (memoAdversary adversary) +
      q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hmemo := (prob_independentTableGame_le_memo adversary).trans_eq
    ((evalDist_independentTableGame_memo adversary).prEvent_eq (· = true))

  exact (forgeAdvantage_deterministic_le_table adversary q hbound).trans (add_le_add hmemo le_rfl)

end XmssSecurity.Seeded
