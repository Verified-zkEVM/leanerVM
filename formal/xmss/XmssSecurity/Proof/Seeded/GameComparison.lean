import XmssSecurity.Proof.Seeded.AdaptiveSeedGuessing

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev KeyMaterial := PublicParameter × ChainSecrets × Digest × ChainSecrets

noncomputable def drawKeyMaterial : ProbComp KeyMaterial := do
  let parameter ← Concrete.samplePublicParameter
  let secret ← Concrete.sampleSecret
  let parameterHigh ← $ᵗ Digest
  let secretHigh ← Concrete.sampleSecret
  return (parameter, secret, parameterHigh, secretHigh)

noncomputable def materialCache (seed : MasterSeed) (material : KeyMaterial) : QueryCache HashSpec :=
  programmedCache seed material.1 material.2.1 material.2.2.1 material.2.2.2

theorem evalDist_programmedGame_seed_last (adversary : Adversary) :
    programmedGame adversary =ᵈ (do
      let material ← drawKeyMaterial
      let seed ← sampleMasterSeed
      (simulateQ romImpl (gameAfterSecrets adversary material.1 material.2.1)).run'
        (materialCache seed material)) := by
  have heq : programmedGame adversary = (do
      let seed ← sampleMasterSeed
      let material ← drawKeyMaterial
      (simulateQ romImpl (gameAfterSecrets adversary material.1 material.2.1)).run'
        (materialCache seed material)) := by
    simp only [programmedGame, drawKeyMaterial, materialCache, bind_assoc, pure_bind]
  rw [heq]
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

theorem evalDist_independentGame_material (adversary : Adversary) :
    ((simulateQ romImpl (gameCore Concrete.scheme adversary)).run' ∅) =ᵈ (do
      let material ← drawKeyMaterial
      (simulateQ romImpl (gameAfterSecrets adversary material.1 material.2.1)).run' ∅) := by
  rw [gameCore_independent_eq, run'_lift_sample_bind]
  unfold drawKeyMaterial
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro parameter
  rw [run'_lift_sample_bind]
  apply EvalDistEq.bind_right
  intro secret
  refine EvalDistEq.symm ?_
  refine (EvalDistEq.bind_right _ fun _ => OracleComp.EvalDistEq.bind_const _ _).trans ?_
  exact OracleComp.EvalDistEq.bind_const _ _

theorem hashQueryBound_gameAfterSecrets (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (parameter : PublicParameter) (secret : ChainSecrets) :
    HashQueryBound (gameAfterSecrets adversary parameter secret) ∅ q := by
  have hpSupport : parameter ∈ support Concrete.samplePublicParameter := by
    rw [OracleComp.support_eq_of_evalDistEq evalDist_samplePublicParameter]
    exact mem_support_uniformSample Digest
  have hsSupport : secret ∈ support Concrete.sampleSecret := by
    unfold Concrete.sampleSecret
    rw [support_uniformSample]
    trivial

  rw [hasHashQueryBound_iff, gameCore_independent_eq] at hbound
  have hp := hashQueryBound_of_sampling_bind Concrete.samplePublicParameter _ ∅ q hbound
    parameter hpSupport
  exact hashQueryBound_of_sampling_bind Concrete.sampleSecret _ ∅ q hp secret hsSupport

/-- The seeded game differs from the independent game by at most one 256-bit guess per hash call. -/
theorem forgeAdvantage_seeded_le_of_independent_budget (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    forgeAdvantage randomizedScheme adversary ≤ forgeAdvantage Concrete.scheme adversary +
      q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  unfold forgeAdvantage
  refine le_of_eq_of_le (((evalDist_gameCore_eq_programmed adversary).trans
    (evalDist_programmedGame_seed_last adversary)).prEvent_eq (· = true)) ?_
  refine le_of_le_of_eq ?_
    (congrArg (· + _) ((evalDist_independentGame_material adversary).prEvent_eq (· = true)).symm)
  apply OracleComp.prEvent_bind_congr_le_add

  intro material _
  exact probEvent_random_cache_change_le _ (fun seed => materialCache seed material) ∅
    (fun seed => programmedCache_agreeOutside seed _ _ _ _) q
    (hashQueryBound_gameAfterSecrets adversary q hbound _ _) (fun value => value = true)

end XmssSecurity.Seeded
