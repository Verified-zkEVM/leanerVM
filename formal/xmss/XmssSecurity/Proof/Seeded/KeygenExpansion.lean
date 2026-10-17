import XmssSecurity.Proof.Seeded.FreshTable
import XmssSecurity.Proof.Seeded.SeedGuessing
import XmssSecurity.Proof.RandomOracle

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

abbrev ChainOutputs := LeafIndex → ChainIndex → HashOutput

def chainInputs (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex) (chain : ChainIndex) :
    HashInput := keygenHashInput parameter (.chain leafIndex chain) seed

theorem chainInputs_injective (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex leafIndex' : LeafIndex) (chain chain' : ChainIndex)
    (h : chainInputs parameter seed leafIndex chain = chainInputs parameter seed leafIndex' chain') :
    leafIndex = leafIndex' ∧ chain = chain' :=
  KeygenDomain.chain.inj (keygenHashInput_injective h).2.1

def parameterCache (seed : MasterSeed) (output : HashOutput) : QueryCache HashSpec :=
  (∅ : QueryCache HashSpec).cacheQuery (keygenHashInput 0 .parameter seed) output

theorem parameterCache_chain_fresh (seed : MasterSeed) (output : HashOutput)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex) :
    parameterCache seed output (chainInputs parameter seed leafIndex chain) = none := by
  have hne : chainInputs parameter seed leafIndex chain ≠ keygenHashInput 0 .parameter seed := by
    intro h
    have hdomain := (keygenHashInput_injective h).2.1
    cases hdomain
  rw [parameterCache]
  exact (QueryCache.cacheQuery_of_ne (spec := HashSpec) ∅ output hne).trans (QueryCache.empty_apply _)

def derivationCache (seed : MasterSeed) (parameterOutput : HashOutput) (outputs : ChainOutputs) :
    QueryCache HashSpec :=
  cacheRows (parameterCache seed parameterOutput) (chainInputs (truncateHash parameterOutput) seed) outputs

/-- The initial cache can differ from an empty oracle only at inputs naming this seed. -/
theorem derivationCache_of_not_seedHit (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : ChainOutputs) (input : HashInput) (hinput : ¬ SeedHit input seed) :
    derivationCache seed parameterOutput outputs input = none := by
  have hparameter : input ≠ keygenHashInput 0 .parameter seed := by
    rintro rfl
    exact hinput (derivationSeedHit_keygen 0 .parameter seed)
  have hchain : ∀ leafIndex chain,
      input ≠ chainInputs (truncateHash parameterOutput) seed leafIndex chain := by
    rintro leafIndex chain rfl
    exact hinput (derivationSeedHit_keygen (truncateHash parameterOutput) (.chain leafIndex chain) seed)
  rw [derivationCache, cacheRows_apply_of_not_mem _ _ _ _ hchain, parameterCache]
  exact (QueryCache.cacheQuery_of_ne (spec := HashSpec) ∅ parameterOutput hparameter).trans
    (QueryCache.empty_apply _)

def deriveChainSecrets (parameter : PublicParameter) (seed : MasterSeed) :
    OracleComp HashSpec (LeafIndex → ChainIndex → Digest) :=
  Concrete.sequenceFin fun leafIndex => Concrete.sequenceFin fun chain =>
    deriveKey parameter (.chain leafIndex chain) seed

noncomputable def drawChainOutputs : ProbComp ChainOutputs :=
  Concrete.sequenceFin fun _ : LeafIndex => Concrete.sequenceFin fun _ : ChainIndex => $ᵗ HashOutput

def outputSecrets (outputs : ChainOutputs) : LeafIndex → ChainIndex → Digest :=
  fun leafIndex chain => truncateHash (outputs leafIndex chain)

theorem deriveChainSecrets_eq_map (parameter : PublicParameter) (seed : MasterSeed) :
    deriveChainSecrets parameter seed =
      outputSecrets <$> Concrete.sequenceFin (fun leafIndex => Concrete.sequenceFin fun chain =>
        (liftM (HashSpec.query (chainInputs parameter seed leafIndex chain)) : OracleComp HashSpec HashOutput)) := by
  simp only [deriveChainSecrets, deriveKey, Concrete.oracleHash, bind_pure_comp,
    sequenceFin_map, chainInputs]
  rfl

/-- The actual WOTS derivation loop, including its final cache, equals fresh full-output sampling. -/
theorem run_deriveChainSecrets (seed : MasterSeed) (parameterOutput : HashOutput) :
    (simulateQ randomOracle (deriveChainSecrets (truncateHash parameterOutput) seed)).run
      (parameterCache seed parameterOutput) =
        (fun outputs => (outputSecrets outputs, derivationCache seed parameterOutput outputs)) <$>
          drawChainOutputs := by
  rw [deriveChainSecrets_eq_map, simulateQ_map, StateT.run_map,
    run_sequenceFin_rows_fresh _
      (fun leafIndex chain leafIndex' chain' => chainInputs_injective _ seed leafIndex leafIndex' chain chain')
      _ (parameterCache_chain_fresh seed parameterOutput _)]
  simp only [bind_pure_comp, Functor.map_map, drawChainOutputs, derivationCache]

theorem evalDist_drawChainOutputs : 𝒮[drawChainOutputs] = 𝒮[$ᵗ ChainOutputs] := by
  calc
    _ = 𝒮[Concrete.sequenceFin fun _ : LeafIndex => ($ᵗ (ChainIndex → HashOutput))] :=
      evalDist_sequenceFin_congr _ _ (fun _ => evalDist_sequenceFin_uniform _)
    _ = _ := evalDist_sequenceFin_uniform _

theorem evalDist_deriveChainSecrets (seed : MasterSeed) (parameterOutput : HashOutput) :
    𝒮[(simulateQ randomOracle (deriveChainSecrets (truncateHash parameterOutput) seed)).run
      (parameterCache seed parameterOutput)] =
        𝒮[(fun outputs => (outputSecrets outputs, derivationCache seed parameterOutput outputs)) <$>
          ($ᵗ ChainOutputs)] := by
  rw [run_deriveChainSecrets, evalSPMF_map, evalSPMF_map, evalDist_drawChainOutputs]

def deriveParametersAndSecrets (seed : MasterSeed) :
    OracleComp HashSpec (PublicParameter × (LeafIndex → ChainIndex → Digest)) := do
  let parameter ← deriveKey 0 .parameter seed
  let secrets ← deriveChainSecrets parameter seed
  return (parameter, secrets)

theorem run_deriveParameter (seed : MasterSeed) :
    (simulateQ randomOracle (deriveKey 0 .parameter seed : OracleComp HashSpec Digest)).run ∅ =
      (fun output => (truncateHash output, parameterCache seed output)) <$> ($ᵗ HashOutput) := by
  have hquery : (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) =
      truncateHash <$> (liftM (HashSpec.query (keygenHashInput 0 .parameter seed)) :
        OracleComp HashSpec HashOutput) := by
    simp only [deriveKey, Concrete.oracleHash, bind_pure_comp]
    rfl
  rw [hquery, simulateQ_map, StateT.run_map, simulateQ_spec_query,
    QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)]
  simp only [Functor.map_map]
  rfl

/-- Exact joint distribution of the derived values and every full answer retained by the oracle. -/
theorem evalDist_deriveParametersAndSecrets (seed : MasterSeed) :
    𝒮[(simulateQ randomOracle (deriveParametersAndSecrets seed)).run ∅] =
      𝒮[do
        let parameterOutput ← $ᵗ HashOutput
        let outputs ← $ᵗ ChainOutputs
        pure ((truncateHash parameterOutput, outputSecrets outputs),
          derivationCache seed parameterOutput outputs)] := by
  simp only [deriveParametersAndSecrets, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [run_deriveParameter]
  simp only [bind_map_left, bind_pure_comp]
  change 𝒮[($ᵗ HashOutput) >>= _] = 𝒮[($ᵗ HashOutput) >>= _]
  apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
  intro parameterOutput
  change 𝒮[(fun result => ((truncateHash parameterOutput, result.1), result.2)) <$>
    (simulateQ randomOracle (deriveChainSecrets (truncateHash parameterOutput) seed)).run
      (parameterCache seed parameterOutput)] = _
  rw [evalSPMF_map, evalDist_deriveChainSecrets, ← evalSPMF_map]
  simp only [Functor.map_map]

end XmssSecurity.Seeded
