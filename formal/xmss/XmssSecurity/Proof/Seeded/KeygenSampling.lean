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
    𝒮[$ᵗ ChainOutputs] = 𝒮[do
      let low ← $ᵗ ChainSecrets
      let high ← $ᵗ ChainSecrets
      pure (chainOutputHalves.symm (high, low))] := by
  calc
    _ = 𝒮[chainOutputHalves.symm <$> ($ᵗ (ChainSecrets × ChainSecrets))] :=
      (evalSPMF_map_bijective_uniform_cross (α := ChainSecrets × ChainSecrets) (β := ChainOutputs)
        chainOutputHalves.symm chainOutputHalves.symm.bijective).symm
    _ = 𝒮[chainOutputHalves.symm <$> (do
        let high ← $ᵗ ChainSecrets
        let low ← $ᵗ ChainSecrets
        pure (high, low))] := by
      rw [evalSPMF_map, evalSPMF_map, evalDist_independent_uniform_pair]
    _ = _ := by
      simp only [map_bind, map_pure]
      exact OracleComp.DeferredSampling.evalSPMF_bind_comm _ _ _

def programmedCache (seed : MasterSeed) (parameter : PublicParameter) (secret : ChainSecrets)
    (parameterHigh : Digest) (secretHigh : ChainSecrets) : QueryCache HashSpec :=
  derivationCache seed (Rom.hashOutputEquivDigestPair.symm (parameterHigh, parameter))
    (chainOutputHalves.symm (secretHigh, secret))

theorem evalDist_parameterOutput_from_halves :
    𝒮[$ᵗ HashOutput] = 𝒮[do
      let low ← $ᵗ Digest
      let high ← $ᵗ Digest
      pure (Rom.hashOutputEquivDigestPair.symm (high, low))] := by
  calc
    _ = 𝒮[Rom.hashOutputEquivDigestPair.symm <$> ($ᵗ (Digest × Digest))] :=
      (evalSPMF_map_bijective_uniform_cross (α := Digest × Digest) (β := HashOutput)
        Rom.hashOutputEquivDigestPair.symm Rom.hashOutputEquivDigestPair.symm.bijective).symm
    _ = 𝒮[Rom.hashOutputEquivDigestPair.symm <$> (do
        let high ← $ᵗ Digest
        let low ← $ᵗ Digest
        pure (high, low))] := by
      rw [evalSPMF_map, evalSPMF_map, evalDist_independent_uniform_pair]
    _ = _ := by
      simp only [map_bind, map_pure]
      exact OracleComp.DeferredSampling.evalSPMF_bind_comm _ _ _

theorem evalDist_samplePublicParameter : 𝒮[Concrete.samplePublicParameter] = 𝒮[$ᵗ Digest] := by
  unfold Concrete.samplePublicParameter
  rw [evalSPMF_uniformSample, evalSPMF_uniformSample]
  rfl

theorem evalDist_sampleSecret : 𝒮[Concrete.sampleSecret] = 𝒮[$ᵗ ChainSecrets] := by
  apply evalSPMF_ext
  intro secret
  unfold Concrete.sampleSecret
  simp only [probOutput_uniformSample]

/-- The same independent parameter and secret sampler as the existing proof, with full derivation answers retained. -/
theorem evalDist_deriveParametersAndSecrets_eq_independent (seed : MasterSeed) :
    𝒮[(simulateQ randomOracle (deriveParametersAndSecrets seed)).run ∅] =
      𝒮[do
        let parameter ← Concrete.samplePublicParameter
        let secret ← Concrete.sampleSecret
        let parameterHigh ← $ᵗ Digest
        let secretHigh ← Concrete.sampleSecret
        pure ((parameter, secret), programmedCache seed parameter secret parameterHigh secretHigh)] := by
  rw [evalDist_deriveParametersAndSecrets]
  trans 𝒮[do
    let parameter ← $ᵗ Digest
    let secret ← $ᵗ ChainSecrets
    let parameterHigh ← $ᵗ Digest
    let secretHigh ← $ᵗ ChainSecrets
    pure ((parameter, secret), programmedCache seed parameter secret parameterHigh secretHigh)]
  · rw [evalSPMF_bind, evalDist_parameterOutput_from_halves, ← evalSPMF_bind]
    simp only [bind_assoc, pure_bind, truncate_from_halves]
    apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
    intro parameter
    trans 𝒮[do
      let parameterHigh ← $ᵗ Digest
      let secret ← $ᵗ ChainSecrets
      let secretHigh ← $ᵗ ChainSecrets
      pure ((parameter, secret), programmedCache seed parameter secret parameterHigh secretHigh)]
    · apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
      intro parameterHigh
      rw [evalSPMF_bind, evalDist_chainOutputs_from_halves, ← evalSPMF_bind]
      simp only [bind_assoc, pure_bind, outputSecrets_from_halves, programmedCache]
    · exact OracleComp.DeferredSampling.evalSPMF_bind_comm _ _ _
  · rw [evalSPMF_bind, evalSPMF_bind, evalDist_samplePublicParameter]
    apply bind_congr
    intro parameter
    rw [evalSPMF_bind, evalSPMF_bind, evalDist_sampleSecret]
    apply bind_congr
    intro secret
    apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
    intro parameterHigh
    rw [evalSPMF_bind, evalSPMF_bind, evalDist_sampleSecret]

end XmssSecurity.Seeded
