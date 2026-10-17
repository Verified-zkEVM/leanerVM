import XmssSecurity.Proof.Seeded.KeygenExpansion

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev ChainSecrets := LeafIndex → ChainIndex → Digest

def chainOutputHalves : ChainOutputs ≃ (ChainSecrets × ChainSecrets) where
  toFun outputs := (fun leafIndex chain => (Rom.hashOutputEquivDigestPair (outputs leafIndex chain)).1,
    outputSecrets outputs)
  invFun halves := fun leafIndex chain =>
    Rom.hashOutputEquivDigestPair.symm (halves.1 leafIndex chain, halves.2 leafIndex chain)
  left_inv outputs := by
    funext leafIndex chain
    exact Rom.hashOutputEquivDigestPair.symm_apply_apply (outputs leafIndex chain)
  right_inv halves := by
    apply Prod.ext <;> funext leafIndex chain
    · exact congrArg Prod.fst (Rom.hashOutputEquivDigestPair.apply_symm_apply
        (halves.1 leafIndex chain, halves.2 leafIndex chain))
    · exact congrArg Prod.snd (Rom.hashOutputEquivDigestPair.apply_symm_apply
        (halves.1 leafIndex chain, halves.2 leafIndex chain))

theorem outputSecrets_from_halves (high low : ChainSecrets) :
    outputSecrets (chainOutputHalves.symm (high, low)) = low :=
  congrArg Prod.snd (chainOutputHalves.apply_symm_apply (high, low))

theorem truncate_from_halves (high low : Digest) :
    truncateHash (Rom.hashOutputEquivDigestPair.symm (high, low)) = low :=
  congrArg Prod.snd (Rom.hashOutputEquivDigestPair.apply_symm_apply (high, low))

theorem evalDist_chainOutputs_from_halves :
    ($ᵗ ChainOutputs) =ᵈ (do
      let low ← $ᵗ ChainSecrets
      let high ← $ᵗ ChainSecrets
      pure (chainOutputHalves.symm (high, low))) := by
  calc
    _ =ᵈ (chainOutputHalves.symm <$> ($ᵗ (ChainSecrets × ChainSecrets))) :=
      (SampleableType.map_uniformSample_evalDistEq_of_bijective
        chainOutputHalves.symm.bijective).symm
    _ =ᵈ (chainOutputHalves.symm <$> (do
        let high ← $ᵗ ChainSecrets
        let low ← $ᵗ ChainSecrets
        pure (high, low))) :=
      evalDist_independent_uniform_pair.symm.map _
    _ =ᵈ _ := by
      simp only [map_bind, map_pure]
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

def programmedCache (seed : MasterSeed) (parameter : PublicParameter) (secret : ChainSecrets)
    (parameterHigh : Digest) (secretHigh : ChainSecrets) : QueryCache HashSpec :=
  derivationCache seed (Rom.hashOutputEquivDigestPair.symm (parameterHigh, parameter))
    (chainOutputHalves.symm (secretHigh, secret))

theorem evalDist_parameterOutput_from_halves :
    ($ᵗ HashOutput) =ᵈ (do
      let low ← $ᵗ Digest
      let high ← $ᵗ Digest
      pure (Rom.hashOutputEquivDigestPair.symm (high, low))) := by
  calc
    _ =ᵈ (Rom.hashOutputEquivDigestPair.symm <$> ($ᵗ (Digest × Digest))) :=
      (SampleableType.map_uniformSample_evalDistEq_of_bijective
        Rom.hashOutputEquivDigestPair.symm.bijective).symm
    _ =ᵈ (Rom.hashOutputEquivDigestPair.symm <$> (do
        let high ← $ᵗ Digest
        let low ← $ᵗ Digest
        pure (high, low))) :=
      evalDist_independent_uniform_pair.symm.map _
    _ =ᵈ _ := by
      simp only [map_bind, map_pure]
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

theorem evalDist_samplePublicParameter : Concrete.samplePublicParameter =ᵈ ($ᵗ Digest) := by
  unfold Concrete.samplePublicParameter
  exact EvalDistEq.of_forall_prEvent_eq (SampleableType.prEvent_uniformSample_inst_irrel _ _)

theorem evalDist_sampleSecret : Concrete.sampleSecret =ᵈ ($ᵗ ChainSecrets) := by
  unfold Concrete.sampleSecret
  exact EvalDistEq.of_forall_prEvent_eq (SampleableType.prEvent_uniformSample_inst_irrel _ _)

/-- The same independent parameter and secret sampler as the existing proof, with full derivation answers retained. -/
theorem evalDist_deriveParametersAndSecrets_eq_independent (seed : MasterSeed) :
    ((simulateQ randomOracle (deriveParametersAndSecrets seed)).run ∅) =ᵈ (do
        let parameter ← Concrete.samplePublicParameter
        let secret ← Concrete.sampleSecret
        let parameterHigh ← $ᵗ Digest
        let secretHigh ← Concrete.sampleSecret
        pure ((parameter, secret), programmedCache seed parameter secret parameterHigh secretHigh)) := by
  refine (evalDist_deriveParametersAndSecrets seed).trans ?_
  refine EvalDistEq.trans (my := (do
    let parameter ← $ᵗ Digest
    let secret ← $ᵗ ChainSecrets
    let parameterHigh ← $ᵗ Digest
    let secretHigh ← $ᵗ ChainSecrets
    pure ((parameter, secret), programmedCache seed parameter secret parameterHigh secretHigh) :
      ProbComp _)) ?_ ?_
  · refine (evalDist_parameterOutput_from_halves.bind_left _).trans ?_
    simp only [bind_assoc, pure_bind, truncate_from_halves]
    apply EvalDistEq.bind_right
    intro parameter
    refine EvalDistEq.trans (my := (do
      let parameterHigh ← $ᵗ Digest
      let secret ← $ᵗ ChainSecrets
      let secretHigh ← $ᵗ ChainSecrets
      pure ((parameter, secret), programmedCache seed parameter secret parameterHigh secretHigh) :
        ProbComp _)) ?_ ?_
    · apply EvalDistEq.bind_right
      intro parameterHigh
      refine (evalDist_chainOutputs_from_halves.bind_left _).trans ?_
      simp only [bind_assoc, pure_bind, outputSecrets_from_halves, programmedCache,
        EvalDistEq.refl]
    · exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  · exact evalDist_samplePublicParameter.symm.bind fun _ =>
      evalDist_sampleSecret.symm.bind fun _ =>
        EvalDistEq.bind_right _ fun _ => evalDist_sampleSecret.symm.bind_left _


end XmssSecurity.Seeded
