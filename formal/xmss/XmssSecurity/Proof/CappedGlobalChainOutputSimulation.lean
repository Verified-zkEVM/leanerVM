import XmssSecurity.Proof.CappedGlobalKeygen
import XmssSecurity.Proof.CappedGlobalTreeCacheCorrespondence

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain


noncomputable def outputChainExtension
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    ProbComp (Vector Digest ((n + 1) + 1) × QueryCache HashSpec) := do
  let output ← $ᵗ HashOutput
  pure (values.push (truncateHash output),
    cache.cacheQuery
      (Concrete.CacheView.chainInput parameter leafIndex chain step values.back)
      output)

theorem evalDist_programmedChainExtension_eq_output
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    evalDist (programmedChainExtension parameter leafIndex chain step values cache) =
      evalDist (outputChainExtension parameter leafIndex chain step values cache) := by
  unfold programmedChainExtension outputChainExtension
  exact Rom.evalDist_sampledHashOutputWithDigest_bind_eq_uniform_bind
    (fun sampled => pure (values.push sampled.1,
      cache.cacheQuery
        (Concrete.CacheView.chainInput parameter leafIndex chain step values.back)
        sampled.2))

noncomputable def outputChainTrajectory
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : Nat) : (steps : Nat) → Digest → QueryCache HashSpec →
      ProbComp (Vector Digest (steps + 1) × QueryCache HashSpec)
  | 0, value, cache => pure (Vector.ofFn (fun _ => value), cache)
  | steps + 1, value, cache => do
      let prior ← outputChainTrajectory parameter leafIndex chain position
        steps value cache
      if hvalid : position + steps < chainLength - 1 then
        outputChainExtension parameter leafIndex chain ⟨position + steps, hvalid⟩
          prior.1 prior.2
      else
        pure (prior.1.push 0, prior.2)

theorem evalDist_programmedChainTrajectory_eq_output
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest)
      (cache : QueryCache HashSpec),
      evalDist (programmedChainTrajectory parameter leafIndex chain position steps
        value cache) =
      evalDist (outputChainTrajectory parameter leafIndex chain position steps
        value cache) := by
  intro steps
  induction steps with
  | zero =>
      intro value cache
      rfl
  | succ steps ih =>
      intro value cache
      rw [programmedChainTrajectory, outputChainTrajectory]
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [ih value cache]
      apply bind_congr
      intro prior
      by_cases hvalid : position + steps < chainLength - 1
      · simp only [hvalid, ↓reduceDIte]
        exact evalDist_programmedChainExtension_eq_output parameter leafIndex chain
          ⟨position + steps, hvalid⟩ prior.1 prior.2
      · simp [hvalid]

noncomputable def outputFixedSeedChainTrajectoriesFromCache
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    QueryCache HashSpec → List LeafIndex →
      ProbComp (List (Vector Digest (steps + 1)) × QueryCache HashSpec)
  | cache, [] => pure ([], cache)
  | cache, leafIndex :: leafIndices => do
      let first ← outputChainTrajectory parameter leafIndex chain 0 steps
        (secret leafIndex chain) cache
      let rest ← outputFixedSeedChainTrajectoriesFromCache parameter secret
        chain steps first.2 leafIndices
      pure (first.1 :: rest.1, rest.2)

theorem outputFixedSeedChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (leafIndices : List LeafIndex) :
    outputFixedSeedChainTrajectoriesFromCache parameter secret chain steps cache
      (leafIndex :: leafIndices) = (do
        let first ← outputChainTrajectory parameter leafIndex chain 0 steps
          (secret leafIndex chain) cache
        let rest ← outputFixedSeedChainTrajectoriesFromCache parameter secret
          chain steps first.2 leafIndices
        pure (first.1 :: rest.1, rest.2)) := rfl

theorem evalDist_programmedFixedSeedChainTrajectories_eq_output
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (leafIndices : List LeafIndex) (cache : QueryCache HashSpec),
      evalDist (programmedFixedSeedChainTrajectoriesFromCache parameter secret
        chain steps cache leafIndices) =
      evalDist (outputFixedSeedChainTrajectoriesFromCache parameter secret chain
        steps cache leafIndices) := by
  intro leafIndices
  induction leafIndices with
  | nil =>
      intro cache
      rfl
  | cons leafIndex leafIndices ih =>
      intro cache
      rw [programmedFixedSeedChainTrajectoriesFromCache_cons,
        outputFixedSeedChainTrajectoriesFromCache_cons]
      calc
        _ = evalDist (outputChainTrajectory parameter leafIndex chain 0 steps
              (secret leafIndex chain) cache >>= fun first =>
            programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
              steps first.2 leafIndices >>= fun rest =>
            pure (first.1 :: rest.1, rest.2)) := by
          rw [evalDist_bind,
            evalDist_programmedChainTrajectory_eq_output parameter leafIndex chain 0
              steps (secret leafIndex chain) cache,
            ← evalDist_bind]
        _ = _ := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          rw [evalDist_bind, ih first.2, ← evalDist_bind]



noncomputable def outputAllChainTrajectoriesFromCache
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    QueryCache HashSpec → List ChainIndex →
      ProbComp (AllChainTrajectories × QueryCache HashSpec)
  | cache, [] => pure (fun _ => [], cache)
  | cache, chain :: chains => do
      let first ← outputFixedSeedChainTrajectoriesFromCache parameter secret
        chain (chainLength - 1) cache allLeafIndices
      let rest ← outputAllChainTrajectoriesFromCache parameter secret first.2
        chains
      pure (Function.update rest.1 chain first.1, rest.2)

theorem outputAllChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (cache : QueryCache HashSpec) (chain : ChainIndex)
    (chains : List ChainIndex) :
    outputAllChainTrajectoriesFromCache parameter secret cache
      (chain :: chains) = (do
        let first ← outputFixedSeedChainTrajectoriesFromCache parameter secret
          chain (chainLength - 1) cache allLeafIndices
        let rest ← outputAllChainTrajectoriesFromCache parameter secret first.2
          chains
        pure (Function.update rest.1 chain first.1, rest.2)) := rfl

theorem evalDist_programmedAllChainTrajectories_eq_output
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec),
      evalDist (programmedAllChainTrajectoriesFromCache parameter secret cache
        chains) =
      evalDist (outputAllChainTrajectoriesFromCache parameter secret cache
        chains) := by
  intro chains
  induction chains with
  | nil =>
      intro cache
      rfl
  | cons chain chains ih =>
      intro cache
      rw [programmedAllChainTrajectoriesFromCache_cons,
        outputAllChainTrajectoriesFromCache_cons]
      calc
        _ = evalDist (outputFixedSeedChainTrajectoriesFromCache parameter secret
              chain (chainLength - 1) cache allLeafIndices >>= fun first =>
            programmedAllChainTrajectoriesFromCache parameter secret first.2
              chains >>= fun rest =>
            pure (Function.update rest.1 chain first.1, rest.2)) := by
          rw [evalDist_bind,
            evalDist_programmedFixedSeedChainTrajectories_eq_output parameter
              secret chain (chainLength - 1) allLeafIndices cache,
            ← evalDist_bind]
        _ = _ := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          rw [evalDist_bind, ih first.2, ← evalDist_bind]



noncomputable def outputGlobalChainTrajectoryMaterial
    (parameter : PublicParameter) : ProbComp GlobalChainTrajectoryMaterial := do
  let secret ← Concrete.sampleSecret
  let trajectories ← outputAllChainTrajectoriesFromCache parameter secret ∅
    allChains
  pure (secret, trajectories)

theorem evalDist_programmedGlobalChainTrajectoryMaterial_eq_output
    (parameter : PublicParameter) :
    evalDist (programmedGlobalChainTrajectoryMaterial parameter) =
      evalDist (outputGlobalChainTrajectoryMaterial parameter) := by
  unfold programmedGlobalChainTrajectoryMaterial
    outputGlobalChainTrajectoryMaterial
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secret
  rw [evalDist_bind,
    evalDist_programmedAllChainTrajectories_eq_output parameter secret allChains
      ∅,
    ← evalDist_bind]

theorem outputGlobalChainTrajectoryMaterial_support_as_programmed
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (outputGlobalChainTrajectoryMaterial parameter)) :
    material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter) :=
  (mem_support_iff_of_evalDist_eq
    (evalDist_programmedGlobalChainTrajectoryMaterial_eq_output parameter)
    material).mpr hmaterial

theorem outputGlobalChainTrajectoryMaterial_support_as_actual
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (outputGlobalChainTrajectoryMaterial parameter)) :
    material.2 ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter material.1 ∅
        allChains) := by
  have hprogrammed :=
    outputGlobalChainTrajectoryMaterial_support_as_programmed parameter material
      hmaterial
  have hprogrammedTrajectories :=
    programmedGlobalChainTrajectoryMaterial_support_trajectories parameter
      material hprogrammed
  have heq := evalDist_allChainTrajectories_eq_programmed parameter material.1
    allChains ∅ allChains_nodup (by simp [AllChainAddressesAbsent])
  exact (mem_support_iff_of_evalDist_eq heq material.2).mpr
    hprogrammedTrajectories

theorem outputGlobalChainTrajectoryMaterial_seedsMatch
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (outputGlobalChainTrajectoryMaterial parameter)) :
    GlobalChainTableSeedsMatch
      (SecretKey.withoutPrecomputation parameter material.1)
      (globalChainTrajectoryMaterialTable material) := by
  have hactual := outputGlobalChainTrajectoryMaterial_support_as_actual
    parameter material hmaterial
  have htable := Concrete.allChainTrajectoriesFromCache_globalTable_eq
    parameter material.1 material.2 material.2.2 hactual le_rfl
  intro leafIndex chain
  rw [globalChainTrajectoryMaterialTable, htable]
  simp [globalKeygenChainValueTable, keygenChainValueTable,
    SecretKey.withoutPrecomputation]

theorem Concrete.allChainTrajectoriesFromCache_edgesMatch
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (result : AllChainTrajectories × QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter secret ∅ allChains)) :
    GlobalChainTableEdgesMatch result.2 parameter
      (globalChainValueTableOfTrajectories result.1) := by
  have htable := Concrete.allChainTrajectoriesFromCache_globalTable_eq
    parameter secret result result.2 hresult le_rfl
  rw [htable]
  rintro ⟨chain, leafIndex, step⟩
  have hrun :=
    Concrete.allChainTrajectoriesFromCache_chainWalk_run_eq_pure
      parameter secret result hresult result.2 le_rfl leafIndex chain
  have hwalk :
      (Concrete.CacheReplay.oneTimePublicKey result.2 parameter secret leafIndex
          chain, result.2) ∈ support
        ((simulateQ randomOracle
          (Concrete.chainWalk parameter leafIndex chain 0 (chainLength - 1)
            (secret leafIndex chain) : OracleComp HashSpec Digest)).run result.2) := by
    rw [hrun]
    simp
  obtain ⟨output, hcached⟩ :=
    Concrete.CacheReplay.chainWalk_query_cached_in_largerCache
      parameter leafIndex chain 0 (chainLength - 1) (secret leafIndex chain)
        step.val step.isLt (by simp) result.2 result.2 result.2
        (Concrete.CacheReplay.oneTimePublicKey result.2 parameter secret leafIndex
          chain) hwalk le_rfl
  have hstepIndex : (⟨0 + step.val, by omega⟩ : ChainStep) = step := by
    apply Fin.ext
    simp
  rw [hstepIndex] at hcached
  refine ⟨output, ?_, ?_⟩
  · convert hcached using 1
    all_goals
      simp [globalChainTableEdgeInput, globalKeygenChainValueTable,
        keygenChainValueTable, chainStepDigit,
        SecretKey.withoutPrecomputation]
  · let stepFunction :=
      Concrete.CacheView.chainStep result.2 parameter leafIndex chain
    calc
      truncateHash output = Concrete.CacheView.digestAt result.2
          (Concrete.CacheView.chainInput parameter leafIndex chain step
            (Wots.walk stepFunction 0 step.val (secret leafIndex chain))) :=
        (Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached).symm
      _ = stepFunction step.val
          (Wots.walk stepFunction 0 step.val (secret leafIndex chain)) := by
        symm
        exact Concrete.CacheView.chainStep_eq result.2 parameter leafIndex chain
          step.val _ step.isLt
      _ = globalChainTableEdgeTarget
          (globalKeygenChainValueTable result.2
            (SecretKey.withoutPrecomputation parameter secret))
          (chain, leafIndex, step) := by
        change stepFunction step.val
            (Wots.walk stepFunction 0 step.val (secret leafIndex chain)) =
          Wots.signChain stepFunction (chainStepNextDigit step)
            (secret leafIndex chain)
        unfold Wots.signChain
        rw [show (chainStepNextDigit step).val = step.val + 1 by
          simp [chainStepNextDigit]]
        simp only [Wots.walk, zero_add]

theorem programmedGlobalChainTrajectoryMaterial_edgesMatch
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    GlobalChainTableEdgesMatch material.2.2 parameter
      (globalChainTrajectoryMaterialTable material) := by
  have hprogrammedTrajectories :=
    programmedGlobalChainTrajectoryMaterial_support_trajectories parameter
      material hmaterial
  have heq := evalDist_allChainTrajectories_eq_programmed parameter material.1
    allChains ∅ allChains_nodup (by simp [AllChainAddressesAbsent])
  have hactual := (mem_support_iff_of_evalDist_eq heq material.2).mpr
    hprogrammedTrajectories
  exact Concrete.allChainTrajectoriesFromCache_edgesMatch parameter material.1
    material.2 hactual

theorem outputGlobalChainTrajectoryMaterial_edgesMatch
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (outputGlobalChainTrajectoryMaterial parameter)) :
    GlobalChainTableEdgesMatch material.2.2 parameter
      (globalChainTrajectoryMaterialTable material) :=
  programmedGlobalChainTrajectoryMaterial_edgesMatch parameter material
    (outputGlobalChainTrajectoryMaterial_support_as_programmed parameter
      material hmaterial)



abbrev OutputTrace (α : Type) := α × List HashOutput

theorem outputTrace_bind_fst
    (first : ProbComp (OutputTrace α))
    (rest : α → List HashOutput → ProbComp (OutputTrace β))
    (erasedFirst : ProbComp α) (erasedRest : α → ProbComp β)
    (combine : α → β → γ)
    (hfirst : Prod.fst <$> first = erasedFirst)
    (hrest : ∀ value outputs,
      Prod.fst <$> rest value outputs = erasedRest value) :
    Prod.fst <$> (do
      let left ← first
      let right ← rest left.1 left.2
      pure (combine left.1 right.1, right.2)) = (do
      let left ← erasedFirst
      let right ← erasedRest left
      pure (combine left right)) := by
  calc
    _ = (first >>= fun left =>
        (Prod.fst <$> rest left.1 left.2) >>= fun right =>
        pure (combine left.1 right)) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = (first >>= fun left =>
        erasedRest left.1 >>= fun right =>
        pure (combine left.1 right)) := by
      apply bind_congr
      intro left
      rw [hrest]
    _ = ((Prod.fst <$> first) >>= fun left =>
        erasedRest left >>= fun right => pure (combine left right)) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = _ := by rw [hfirst]

theorem evalDist_outputTrace_bind_snd
    (first : ProbComp (OutputTrace α))
    (rest : α → List HashOutput → ProbComp (OutputTrace β))
    (combine : α → β → γ) (outputs : List HashOutput)
    (firstCount secondCount : Nat)
    (hfirst : evalDist (Prod.snd <$> first) =
      evalDist ((outputs ++ ·) <$>
        uniformSnocList HashOutput firstCount))
    (hrest : ∀ value nextOutputs,
      evalDist (Prod.snd <$> rest value nextOutputs) =
      evalDist ((nextOutputs ++ ·) <$>
        uniformSnocList HashOutput secondCount)) :
    evalDist (Prod.snd <$> (do
      let left ← first
      let right ← rest left.1 left.2
      pure (combine left.1 right.1, right.2))) =
    evalDist ((outputs ++ ·) <$>
      uniformSnocList HashOutput (firstCount + secondCount)) := by
  calc
    _ = evalDist (first >>= fun left =>
        Prod.snd <$> rest left.1 left.2) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (first >>= fun left =>
        (left.2 ++ ·) <$> uniformSnocList HashOutput secondCount) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro left
      exact hrest left.1 left.2
    _ = evalDist ((Prod.snd <$> first) >>= fun leftOutputs =>
        (leftOutputs ++ ·) <$>
          uniformSnocList HashOutput secondCount) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (((outputs ++ ·) <$>
          uniformSnocList HashOutput firstCount) >>= fun leftOutputs =>
        (leftOutputs ++ ·) <$>
          uniformSnocList HashOutput secondCount) := by
      rw [evalDist_bind, hfirst, ← evalDist_bind]
    _ = evalDist ((outputs ++ ·) <$>
        (do
          let left ← uniformSnocList HashOutput firstCount
          let right ← uniformSnocList HashOutput secondCount
          pure (left ++ right))) := by
      simp [map_eq_bind_pure_comp, bind_assoc, List.append_assoc]
    _ = _ := by rw [uniformSnocList_append]

noncomputable def outputChainTrajectoryTrace
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : Nat) : (steps : Nat) → Digest → QueryCache HashSpec →
      List HashOutput →
      ProbComp (OutputTrace (Vector Digest (steps + 1) × QueryCache HashSpec))
  | 0, value, cache, outputs =>
      pure ((Vector.ofFn (fun _ => value), cache), outputs)
  | steps + 1, value, cache, outputs => do
      let prior ← outputChainTrajectoryTrace parameter leafIndex chain position
        steps value cache outputs
      if hvalid : position + steps < chainLength - 1 then
        let output ← $ᵗ HashOutput
        pure ((prior.1.1.push (truncateHash output),
          prior.1.2.cacheQuery
            (Concrete.CacheView.chainInput parameter leafIndex chain
              ⟨position + steps, hvalid⟩ prior.1.1.back)
            output), prior.2 ++ [output])
      else
        pure ((prior.1.1.push 0, prior.1.2), prior.2)

noncomputable def outputFixedSeedChainTrajectoriesTrace
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    QueryCache HashSpec → List LeafIndex → List HashOutput →
      ProbComp (OutputTrace
        (List (Vector Digest (steps + 1)) × QueryCache HashSpec))
  | cache, [], outputs => pure (([], cache), outputs)
  | cache, leafIndex :: leafIndices, outputs => do
      let first ← outputChainTrajectoryTrace parameter leafIndex chain 0 steps
        (secret leafIndex chain) cache outputs
      let rest ← outputFixedSeedChainTrajectoriesTrace parameter secret chain
        steps first.1.2 leafIndices first.2
      pure ((first.1.1 :: rest.1.1, rest.1.2), rest.2)

noncomputable def outputAllChainTrajectoriesTrace
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    QueryCache HashSpec → List ChainIndex → List HashOutput →
      ProbComp (OutputTrace (AllChainTrajectories × QueryCache HashSpec))
  | cache, [], outputs => pure ((fun _ => [], cache), outputs)
  | cache, chain :: chains, outputs => do
      let first ← outputFixedSeedChainTrajectoriesTrace parameter secret chain
        (chainLength - 1) cache allLeafIndices outputs
      let rest ← outputAllChainTrajectoriesTrace parameter secret first.1.2
        chains first.2
      pure ((Function.update rest.1.1 chain first.1.1, rest.1.2), rest.2)

noncomputable def outputGlobalChainTrajectoryMaterialTrace
    (parameter : PublicParameter) :
    ProbComp (OutputTrace GlobalChainTrajectoryMaterial) := do
  let secret ← Concrete.sampleSecret
  let trajectories ← outputAllChainTrajectoriesTrace parameter secret ∅
    allChains []
  let material : GlobalChainTrajectoryMaterial :=
    (secret, (trajectories.1.1, trajectories.1.2))
  pure (material, trajectories.2)

theorem outputChainTrajectoryTrace_fst
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest)
      (cache : QueryCache HashSpec) (outputs : List HashOutput),
      Prod.fst <$> outputChainTrajectoryTrace parameter leafIndex chain position
        steps value cache outputs =
      outputChainTrajectory parameter leafIndex chain position steps value cache := by
  intro steps
  induction steps with
  | zero =>
      intro value cache outputs
      simp [outputChainTrajectoryTrace, outputChainTrajectory]
  | succ steps ih =>
      intro value cache outputs
      rw [outputChainTrajectoryTrace, outputChainTrajectory]
      calc
        _ = ((Prod.fst <$> outputChainTrajectoryTrace parameter leafIndex chain
              position steps value cache outputs) >>= fun prior =>
            if hvalid : position + steps < chainLength - 1 then
              outputChainExtension parameter leafIndex chain
                ⟨position + steps, hvalid⟩ prior.1 prior.2
            else
              pure (prior.1.push 0, prior.2)) := by
          by_cases hvalid : position + steps < chainLength - 1
          · simp [hvalid, outputChainExtension, map_eq_bind_pure_comp,
              bind_assoc]
          · simp [hvalid, map_eq_bind_pure_comp, bind_assoc]
        _ = _ := by rw [ih value cache outputs]

theorem outputFixedSeedChainTrajectoriesTrace_fst
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) : ∀ (leafIndices : List LeafIndex)
      (cache : QueryCache HashSpec) (outputs : List HashOutput),
      Prod.fst <$> outputFixedSeedChainTrajectoriesTrace parameter secret chain
        steps cache leafIndices outputs =
      outputFixedSeedChainTrajectoriesFromCache parameter secret chain steps
        cache leafIndices := by
  intro leafIndices
  induction leafIndices with
  | nil =>
      intro cache outputs
      simp [outputFixedSeedChainTrajectoriesTrace,
        outputFixedSeedChainTrajectoriesFromCache]
  | cons leafIndex leafIndices ih =>
      intro cache outputs
      rw [outputFixedSeedChainTrajectoriesTrace,
        outputFixedSeedChainTrajectoriesFromCache]
      exact outputTrace_bind_fst
        (outputChainTrajectoryTrace parameter leafIndex chain 0 steps
          (secret leafIndex chain) cache outputs)
        (fun first nextOutputs =>
          outputFixedSeedChainTrajectoriesTrace parameter secret chain steps
            first.2 leafIndices nextOutputs)
        (outputChainTrajectory parameter leafIndex chain 0 steps
          (secret leafIndex chain) cache)
        (fun first => outputFixedSeedChainTrajectoriesFromCache parameter secret
          chain steps first.2 leafIndices)
        (fun first rest => (first.1 :: rest.1, rest.2))
        (outputChainTrajectoryTrace_fst parameter leafIndex chain 0 steps
          (secret leafIndex chain) cache outputs)
        (fun first nextOutputs => ih first.2 nextOutputs)

theorem outputAllChainTrajectoriesTrace_fst
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec)
      (outputs : List HashOutput),
      Prod.fst <$> outputAllChainTrajectoriesTrace parameter secret cache chains
        outputs =
      outputAllChainTrajectoriesFromCache parameter secret cache chains := by
  intro chains
  induction chains with
  | nil =>
      intro cache outputs
      simp [outputAllChainTrajectoriesTrace,
        outputAllChainTrajectoriesFromCache]
  | cons chain chains ih =>
      intro cache outputs
      rw [outputAllChainTrajectoriesTrace,
        outputAllChainTrajectoriesFromCache]
      exact outputTrace_bind_fst
        (outputFixedSeedChainTrajectoriesTrace parameter secret chain
          (chainLength - 1) cache allLeafIndices outputs)
        (fun first nextOutputs => outputAllChainTrajectoriesTrace parameter
          secret first.2 chains nextOutputs)
        (outputFixedSeedChainTrajectoriesFromCache parameter secret chain
          (chainLength - 1) cache allLeafIndices)
        (fun first => outputAllChainTrajectoriesFromCache parameter secret
          first.2 chains)
        (fun first rest =>
          (Function.update rest.1 chain first.1, rest.2))
        (outputFixedSeedChainTrajectoriesTrace_fst parameter secret chain
          (chainLength - 1) allLeafIndices cache outputs)
        (fun first nextOutputs => ih first.2 nextOutputs)

theorem outputGlobalChainTrajectoryMaterialTrace_fst
    (parameter : PublicParameter) :
    Prod.fst <$> outputGlobalChainTrajectoryMaterialTrace parameter =
      outputGlobalChainTrajectoryMaterial parameter := by
  unfold outputGlobalChainTrajectoryMaterialTrace
    outputGlobalChainTrajectoryMaterial
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro secret
  rw [← outputAllChainTrajectoriesTrace_fst parameter secret allChains ∅ []]
  simp [map_eq_bind_pure_comp, bind_assoc]

theorem evalDist_outputChainTrajectoryTrace_snd
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest)
      (cache : QueryCache HashSpec) (outputs : List HashOutput),
      position + steps ≤ chainLength - 1 →
      evalDist (Prod.snd <$> outputChainTrajectoryTrace parameter leafIndex chain
        position steps value cache outputs) =
      evalDist ((outputs ++ ·) <$> uniformSnocList HashOutput steps) := by
  intro steps
  induction steps with
  | zero =>
      intro value cache outputs _hsteps
      simp [outputChainTrajectoryTrace, uniformSnocList]
  | succ steps ih =>
      intro value cache outputs hsteps
      have hvalid : position + steps < chainLength - 1 := by omega
      rw [outputChainTrajectoryTrace]
      simp only [hvalid, ↓reduceDIte]
      calc
        _ = evalDist ((Prod.snd <$> outputChainTrajectoryTrace parameter leafIndex
              chain position steps value cache outputs) >>= fun prior =>
            ($ᵗ HashOutput) >>= fun output => pure (prior ++ [output])) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist (((outputs ++ ·) <$>
              uniformSnocList HashOutput steps) >>= fun prior =>
            ($ᵗ HashOutput) >>= fun output => pure (prior ++ [output])) := by
          rw [evalDist_bind, ih value cache outputs (by omega), ← evalDist_bind]
        _ = evalDist ((outputs ++ ·) <$>
              uniformSnocList HashOutput (steps + 1)) := by
          simp [uniformSnocList, map_eq_bind_pure_comp, bind_assoc,
            List.append_assoc]

theorem evalDist_outputFixedSeedChainTrajectoriesTrace_snd
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1) :
    ∀ (leafIndices : List LeafIndex) (cache : QueryCache HashSpec)
      (outputs : List HashOutput),
      evalDist (Prod.snd <$> outputFixedSeedChainTrajectoriesTrace parameter
        secret chain steps cache leafIndices outputs) =
      evalDist ((outputs ++ ·) <$>
        uniformSnocList HashOutput (leafIndices.length * steps)) := by
  intro leafIndices
  induction leafIndices with
  | nil =>
      intro cache outputs
      simp [outputFixedSeedChainTrajectoriesTrace, uniformSnocList]
  | cons leafIndex leafIndices ih =>
      intro cache outputs
      rw [outputFixedSeedChainTrajectoriesTrace]
      calc
        _ = evalDist ((outputs ++ ·) <$> uniformSnocList HashOutput
              (steps + leafIndices.length * steps)) :=
          evalDist_outputTrace_bind_snd
            (outputChainTrajectoryTrace parameter leafIndex chain 0 steps
              (secret leafIndex chain) cache outputs)
            (fun first nextOutputs =>
              outputFixedSeedChainTrajectoriesTrace parameter secret chain
                steps first.2 leafIndices nextOutputs)
            (fun first rest => (first.1 :: rest.1, rest.2)) outputs steps
            (leafIndices.length * steps)
            (evalDist_outputChainTrajectoryTrace_snd parameter leafIndex chain 0
              steps (secret leafIndex chain) cache outputs
                (by simpa using hsteps))
            (fun first nextOutputs => ih first.2 nextOutputs)
        _ = _ := by
          congr 3
          simp [Nat.succ_mul, Nat.add_comm]

theorem evalDist_outputAllChainTrajectoriesTrace_snd
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec)
      (outputs : List HashOutput),
      evalDist (Prod.snd <$> outputAllChainTrajectoriesTrace parameter secret
        cache chains outputs) =
      evalDist ((outputs ++ ·) <$> uniformSnocList HashOutput
        (chains.length * (allLeafIndices.length * (chainLength - 1)))) := by
  intro chains
  induction chains with
  | nil =>
      intro cache outputs
      simp [outputAllChainTrajectoriesTrace, uniformSnocList]
  | cons chain chains ih =>
      intro cache outputs
      rw [outputAllChainTrajectoriesTrace]
      let blockSize := allLeafIndices.length * (chainLength - 1)
      calc
        _ = evalDist ((outputs ++ ·) <$> uniformSnocList HashOutput
              (blockSize + chains.length * blockSize)) :=
          evalDist_outputTrace_bind_snd
            (outputFixedSeedChainTrajectoriesTrace parameter secret chain
              (chainLength - 1) cache allLeafIndices outputs)
            (fun first nextOutputs => outputAllChainTrajectoriesTrace parameter
              secret first.2 chains nextOutputs)
            (fun first rest =>
              (Function.update rest.1 chain first.1, rest.2))
            outputs blockSize (chains.length * blockSize)
            (evalDist_outputFixedSeedChainTrajectoriesTrace_snd parameter secret
              chain (chainLength - 1) le_rfl allLeafIndices cache outputs)
            (fun first nextOutputs => ih first.2 nextOutputs)
        _ = _ := by
          congr 3
          simp [blockSize, Nat.succ_mul, Nat.add_comm]

noncomputable def outputTraceRandomness
    (trace : OutputTrace GlobalChainTrajectoryMaterial) :
    (LeafIndex → ChainIndex → Digest) × GlobalChainEdgeOutputTable :=
  (trace.1.1, globalChainEdgeOutputTableOfOutputTape trace.2)

theorem evalDist_outputTraceRandomness_eq_uniform
    (parameter : PublicParameter) :
    evalDist (outputTraceRandomness <$>
      outputGlobalChainTrajectoryMaterialTrace parameter) =
    evalDist uniformGlobalChainKeygenRandomness := by
  let secretMeasure :=
    (liftM (PMF.uniformOfFintype (LeafIndex → ChainIndex → Digest)) :
      SPMF (LeafIndex → ChainIndex → Digest))
  let outputTableMeasure :=
    (liftM (PMF.uniformOfFintype GlobalChainEdgeOutputTable) :
      SPMF GlobalChainEdgeOutputTable)
  have hconditional (secret : LeafIndex → ChainIndex → Digest) :
      evalDist ((fun result =>
        (secret, globalChainEdgeOutputTableOfOutputTape result.2)) <$>
          outputAllChainTrajectoriesTrace parameter secret ∅ allChains []) =
      (fun table => (secret, table)) <$> outputTableMeasure := by
    let trace := outputAllChainTrajectoriesTrace parameter secret ∅ allChains []
    have htape : evalDist (Prod.snd <$> trace) =
        evalDist (uniformSnocList HashOutput globalOutputEdgeOrder.length) := by
      calc
        _ = evalDist (uniformSnocList HashOutput
            (allChains.length *
              (allLeafIndices.length * (chainLength - 1)))) := by
          simpa [trace] using
            evalDist_outputAllChainTrajectoriesTrace_snd parameter secret
              allChains ∅ []
        _ = _ := by rw [globalOutputEdgeOrder_length]
    calc
      _ = evalDist ((fun table => (secret, table)) <$>
          (globalChainEdgeOutputTableOfOutputTape <$>
            (Prod.snd <$> trace))) := by
        simp [trace, Functor.map_map]
      _ = (fun table => (secret, table)) <$>
          (globalChainEdgeOutputTableOfOutputTape <$>
            evalDist (Prod.snd <$> trace)) := by
        rw [evalDist_map, evalDist_map]
      _ = (fun table => (secret, table)) <$>
          (globalChainEdgeOutputTableOfOutputTape <$>
            evalDist (uniformSnocList HashOutput
              globalOutputEdgeOrder.length)) :=
        congrArg (fun distribution => (fun table => (secret, table)) <$>
          (globalChainEdgeOutputTableOfOutputTape <$> distribution)) htape
      _ = (fun table => (secret, table)) <$>
          evalDist (globalChainEdgeOutputTableOfOutputTape <$>
            uniformSnocList HashOutput globalOutputEdgeOrder.length) := by
        rw [evalDist_map]
      _ = (fun table => (secret, table)) <$> outputTableMeasure := by
        exact congrArg (fun distribution =>
          (fun table => (secret, table)) <$> distribution)
            evalDist_globalChainEdgeOutputTableOfOutputTape_uniformSnoc_eq_uniform
  calc
    _ = evalDist Concrete.sampleSecret >>= fun secret =>
        (fun table => (secret, table)) <$> outputTableMeasure := by
      unfold outputTraceRandomness outputGlobalChainTrajectoryMaterialTrace
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply, evalDist_bind]
      apply bind_congr
      intro secret
      simpa [evalDist_map, map_eq_bind_pure_comp] using hconditional secret
    _ = secretMeasure >>= fun secret =>
        outputTableMeasure >>= fun table => pure (secret, table) := by
      rw [Concrete.evalDist_sampleSecret_eq_uniformMeasure]
      simp [secretMeasure, outputTableMeasure]
    _ = (liftM (PMF.uniformOfFintype
          ((LeafIndex → ChainIndex → Digest) × GlobalChainEdgeOutputTable)) :
        SPMF ((LeafIndex → ChainIndex → Digest) ×
          GlobalChainEdgeOutputTable)) := by
      exact uniformMeasure_prod
        (LeafIndex → ChainIndex → Digest) GlobalChainEdgeOutputTable
    _ = evalDist uniformGlobalChainKeygenRandomness :=
      evalDist_uniformGlobalChainKeygenRandomness_eq_uniformMeasure.symm

theorem outputChainTrajectoryTrace_support_info
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest)
      (cache : QueryCache HashSpec) (initialOutputs : List HashOutput)
      (hsteps : position + steps ≤ chainLength - 1),
      ∀
      (result : OutputTrace
        (Vector Digest (steps + 1) × QueryCache HashSpec)),
      result ∈ support (outputChainTrajectoryTrace parameter leafIndex chain
        position steps value cache initialOutputs) →
      ∃ sampled : Fin steps → HashOutput,
        result.2 = initialOutputs ++ List.ofFn sampled ∧
        ∀ index : Fin steps,
          result.1.1[index.succ] = truncateHash (sampled index) ∧
          result.1.2
              (Concrete.CacheView.chainInput parameter leafIndex chain
                ⟨position + index.val, by omega⟩
                result.1.1[index.castSucc]) =
            some (sampled index) := by
  intro steps
  induction steps with
  | zero =>
      intro value cache initialOutputs _hsteps result hresult
      simp only [outputChainTrajectoryTrace, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      refine ⟨Fin.elim0, by simp, ?_⟩
      exact fun index => Fin.elim0 index
  | succ steps ih =>
      intro value cache initialOutputs hsteps result hresult
      have hvalid : position + steps < chainLength - 1 := by omega
      rw [outputChainTrajectoryTrace, mem_support_bind_iff] at hresult
      obtain ⟨prior, hprior, hrest⟩ := hresult
      simp only [hvalid, ↓reduceDIte, mem_support_bind_iff] at hrest
      obtain ⟨output, _houtput, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      obtain ⟨sampled, htape, hsampled⟩ :=
        ih value cache initialOutputs (by omega) prior hprior
      let extended : Fin (steps + 1) → HashOutput :=
        Fin.lastCases output sampled
      refine ⟨extended, ?_, ?_⟩
      · rw [htape, List.ofFn_succ']
        simp [extended, List.append_assoc]
      · intro index
        refine Fin.lastCases ?_ (fun priorIndex => ?_) index
        · dsimp only [Prod.fst, Prod.snd]
          constructor
          · simp [extended]
          · have hsource :
                (prior.1.1.push
                  (truncateHash output))[(Fin.last steps).castSucc] =
                    prior.1.1.back := by
              simp [Vector.back]
            rw [hsource]
            let input := Concrete.CacheView.chainInput parameter leafIndex chain
                ⟨position + steps, hvalid⟩ prior.1.1.back
            convert QueryCache.cacheQuery_self prior.1.2 input output using 1 <;>
              simp [input, extended]
        · dsimp only [Prod.fst, Prod.snd]
          have hpriorInfo := hsampled priorIndex
          constructor
          · simpa [extended] using hpriorInfo.1
          · have hsource :
                (prior.1.1.push
                  (truncateHash output))[priorIndex.castSucc.castSucc] =
                    prior.1.1[priorIndex.castSucc] := by
              simp
            rw [hsource]
            let priorStep : ChainStep :=
                ⟨position + priorIndex.val, by omega⟩
            let newStep : ChainStep := ⟨position + steps, hvalid⟩
            let priorInput := Concrete.CacheView.chainInput parameter leafIndex
              chain priorStep prior.1.1[priorIndex.castSucc]
            let newInput := Concrete.CacheView.chainInput parameter leafIndex chain
              newStep prior.1.1.back
            have hinputNe : priorInput ≠ newInput := by
              intro heq
              have hparts := (Concrete.CacheView.chainInput_eq_iff parameter
                leafIndex leafIndex chain chain priorStep newStep
                prior.1.1[priorIndex.castSucc] prior.1.1.back).mp heq
              have hstep := congrArg Fin.val hparts.2.2.1
              simp [priorStep, newStep] at hstep
              omega
            have hcache : (prior.1.2.cacheQuery newInput output) priorInput =
                some (sampled priorIndex) := by
              rw [QueryCache.cacheQuery_of_ne _ _ hinputNe]
              simpa [priorInput, priorStep] using hpriorInfo.2
            simpa [priorInput, newInput, priorStep, newStep, extended] using
              hcache

def chainTrajectoryOutputTable
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (trajectory : FullChainTrajectory) (cache : QueryCache HashSpec) :
    ChainStep → HashOutput := fun step =>
  (cache (Concrete.CacheView.chainInput parameter leafIndex chain step
    (trajectory.get step.castSucc))).getD 0

theorem outputChainTrajectoryTrace_full_tape
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (value : Digest) (cache : QueryCache HashSpec)
    (initialOutputs : List HashOutput)
    (result : OutputTrace (FullChainTrajectory × QueryCache HashSpec))
    (hresult : result ∈ support
      (outputChainTrajectoryTrace parameter leafIndex chain 0 (chainLength - 1)
        value cache initialOutputs)) :
    result.2 = initialOutputs ++ outputChainSteps.map
      (chainTrajectoryOutputTable parameter leafIndex chain result.1.1
        result.1.2) := by
  obtain ⟨sampled, htape, hsampled⟩ :=
    outputChainTrajectoryTrace_support_info parameter leafIndex chain 0
      (chainLength - 1) value cache initialOutputs le_rfl result hresult
  rw [htape]
  congr 1
  rw [show outputChainSteps.map
      (chainTrajectoryOutputTable parameter leafIndex chain result.1.1 result.1.2) =
      List.ofFn (chainTrajectoryOutputTable parameter leafIndex chain result.1.1
        result.1.2) by simp [outputChainSteps]]
  congr 1
  funext step
  have hinfo := hsampled step
  have hstep : (⟨0 + step.val, by omega⟩ : ChainStep) = step := by
    apply Fin.ext
    simp
  rw [hstep] at hinfo
  have hcache : result.1.2
      (Concrete.CacheView.chainInput parameter leafIndex chain step
        (result.1.1.get step.castSucc)) = some (sampled step) :=
    hinfo.2
  simp [chainTrajectoryOutputTable, hcache]

theorem outputChainTrajectoryTrace_preserves_other
    (parameter : PublicParameter) (leafIndex targetLeafIndex : LeafIndex)
    (chain targetChain : ChainIndex) (targetStep : ChainStep)
    (targetValue : Digest) (hother : targetLeafIndex ≠ leafIndex ∨ targetChain ≠ chain)
    (position steps : Nat) (value : Digest) (cache : QueryCache HashSpec)
    (initialOutputs : List HashOutput)
    (result : OutputTrace
      (Vector Digest (steps + 1) × QueryCache HashSpec))
    (hresult : result ∈ support
      (outputChainTrajectoryTrace parameter leafIndex chain position steps value
        cache initialOutputs)) :
    result.1.2 (Concrete.CacheView.chainInput parameter targetLeafIndex targetChain
        targetStep targetValue) =
      cache (Concrete.CacheView.chainInput parameter targetLeafIndex targetChain
        targetStep targetValue) := by
  induction steps with
  | zero =>
      simp only [outputChainTrajectoryTrace, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | succ steps ih =>
      rw [outputChainTrajectoryTrace, mem_support_bind_iff] at hresult
      obtain ⟨prior, hprior, hrest⟩ := hresult
      split at hrest
      · rename_i hvalid
        rw [mem_support_bind_iff] at hrest
        obtain ⟨output, _houtput, hpure⟩ := hrest
        simp only [support_pure, Set.mem_singleton_iff] at hpure
        subst result
        dsimp only [Prod.fst, Prod.snd]
        have hinputNe :
            Concrete.CacheView.chainInput parameter targetLeafIndex targetChain
                targetStep targetValue ≠
              Concrete.CacheView.chainInput parameter leafIndex chain
                ⟨position + steps, hvalid⟩ prior.1.1.back := by
          intro heq
          have hparts := (Concrete.CacheView.chainInput_eq_iff parameter
            targetLeafIndex leafIndex targetChain chain targetStep
            ⟨position + steps, hvalid⟩ targetValue prior.1.1.back).mp heq
          exact hother.elim (· hparts.1) (· hparts.2.1)
        rw [QueryCache.cacheQuery_of_ne _ _ hinputNe]
        exact ih prior hprior
      · simp only [support_pure, Set.mem_singleton_iff] at hrest
        subst result
        dsimp only [Prod.fst, Prod.snd]
        exact ih prior hprior

theorem outputFixedSeedChainTrajectoriesTrace_preserves_other
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (chain targetChain : ChainIndex) (targetLeafIndex : LeafIndex)
    (targetStep : ChainStep) (targetValue : Digest) (steps : Nat)
    (leafIndices : List LeafIndex) (cache : QueryCache HashSpec)
    (initialOutputs : List HashOutput)
    (result : OutputTrace
      (List (Vector Digest (steps + 1)) × QueryCache HashSpec))
    (hother : targetChain ≠ chain ∨ targetLeafIndex ∉ leafIndices)
    (hresult : result ∈ support
      (outputFixedSeedChainTrajectoriesTrace parameter secret chain steps cache
        leafIndices initialOutputs)) :
    result.1.2 (Concrete.CacheView.chainInput parameter targetLeafIndex targetChain
        targetStep targetValue) =
      cache (Concrete.CacheView.chainInput parameter targetLeafIndex targetChain
        targetStep targetValue) := by
  induction leafIndices generalizing cache initialOutputs result with
  | nil =>
      simp only [outputFixedSeedChainTrajectoriesTrace, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | cons leafIndex leafIndices ih =>
      rw [outputFixedSeedChainTrajectoriesTrace,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hheadOther : targetLeafIndex ≠ leafIndex ∨ targetChain ≠ chain := by
        rcases hother with hchain | hleafIndices
        · exact Or.inr hchain
        · exact Or.inl (fun heq => hleafIndices (by simp [heq]))
      have htailOther : targetChain ≠ chain ∨ targetLeafIndex ∉ leafIndices := by
        rcases hother with hchain | hleafIndices
        · exact Or.inl hchain
        · exact Or.inr (fun hmem => hleafIndices (by simp [hmem]))
      calc
        rest.1.2 (Concrete.CacheView.chainInput parameter targetLeafIndex
            targetChain targetStep targetValue) =
            first.1.2 (Concrete.CacheView.chainInput parameter targetLeafIndex
              targetChain targetStep targetValue) :=
          ih first.1.2 first.2 rest htailOther hrest
        _ = cache (Concrete.CacheView.chainInput parameter targetLeafIndex
            targetChain targetStep targetValue) :=
          outputChainTrajectoryTrace_preserves_other parameter leafIndex
            targetLeafIndex chain targetChain targetStep targetValue hheadOther 0
              steps (secret leafIndex chain) cache initialOutputs first hfirst

theorem outputAllChainTrajectoriesTrace_preserves_other
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetChain : ChainIndex) (targetLeafIndex : LeafIndex)
    (targetStep : ChainStep) (targetValue : Digest)
    (chains : List ChainIndex) (cache : QueryCache HashSpec)
    (initialOutputs : List HashOutput)
    (result : OutputTrace (AllChainTrajectories × QueryCache HashSpec))
    (hother : targetChain ∉ chains)
    (hresult : result ∈ support
      (outputAllChainTrajectoriesTrace parameter secret cache chains
        initialOutputs)) :
    result.1.2 (Concrete.CacheView.chainInput parameter targetLeafIndex targetChain
        targetStep targetValue) =
      cache (Concrete.CacheView.chainInput parameter targetLeafIndex targetChain
        targetStep targetValue) := by
  induction chains generalizing cache initialOutputs result with
  | nil =>
      simp only [outputAllChainTrajectoriesTrace, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | cons chain chains ih =>
      rw [outputAllChainTrajectoriesTrace, mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hhead : targetChain ≠ chain :=
        fun heq => hother (by simp [heq])
      have htail : targetChain ∉ chains :=
        fun hmem => hother (by simp [hmem])
      calc
        rest.1.2 (Concrete.CacheView.chainInput parameter targetLeafIndex
            targetChain targetStep targetValue) =
            first.1.2 (Concrete.CacheView.chainInput parameter targetLeafIndex
              targetChain targetStep targetValue) :=
          ih first.1.2 first.2 rest htail hrest
        _ = cache (Concrete.CacheView.chainInput parameter targetLeafIndex
            targetChain targetStep targetValue) :=
          outputFixedSeedChainTrajectoriesTrace_preserves_other parameter
            secret chain targetChain targetLeafIndex targetStep targetValue
              (chainLength - 1) allLeafIndices cache initialOutputs first
                (Or.inl hhead) hfirst

def fixedChainOutputTape
    (parameter : PublicParameter) (chain : ChainIndex) :
    List LeafIndex → List FullChainTrajectory → QueryCache HashSpec →
      List HashOutput
  | [], _, _ => []
  | _, [], _ => []
  | leafIndex :: leafIndices, trajectory :: trajectories, cache =>
      outputChainSteps.map
          (chainTrajectoryOutputTable parameter leafIndex chain trajectory cache) ++
        fixedChainOutputTape parameter chain leafIndices trajectories cache

theorem outputFixedSeedChainTrajectoriesTrace_full_tape
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (chain : ChainIndex) : ∀ (leafIndices : List LeafIndex), leafIndices.Nodup →
    ∀ (cache : QueryCache HashSpec) (initialOutputs : List HashOutput)
      (result : OutputTrace
        (List FullChainTrajectory × QueryCache HashSpec)),
      result ∈ support
        (outputFixedSeedChainTrajectoriesTrace parameter secret chain
          (chainLength - 1) cache leafIndices initialOutputs) →
      result.2 = initialOutputs ++
        fixedChainOutputTape parameter chain leafIndices result.1.1 result.1.2 := by
  intro leafIndices hnodup
  induction leafIndices with
  | nil =>
      intro cache initialOutputs result hresult
      simp only [outputFixedSeedChainTrajectoriesTrace, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [fixedChainOutputTape]
  | cons leafIndex leafIndices ih =>
      intro cache initialOutputs result hresult
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      rw [outputFixedSeedChainTrajectoriesTrace,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hfirstTape := outputChainTrajectoryTrace_full_tape parameter leafIndex
        chain (secret leafIndex chain) cache initialOutputs first hfirst
      have hrestTape := ih htail first.1.2 first.2 rest hrest
      have hblock : outputChainSteps.map
          (chainTrajectoryOutputTable parameter leafIndex chain first.1.1
            first.1.2) =
          outputChainSteps.map
          (chainTrajectoryOutputTable parameter leafIndex chain first.1.1
            rest.1.2) := by
        apply List.map_congr_left
        intro step _hstep
        unfold chainTrajectoryOutputTable
        have hpreserve :=
          outputFixedSeedChainTrajectoriesTrace_preserves_other parameter
            secret chain chain leafIndex step (first.1.1.get step.castSucc)
              (chainLength - 1) leafIndices first.1.2 first.2 rest
                (Or.inr hhead) hrest
        rw [hpreserve]
      rw [hrestTape, hfirstTape, hblock]
      simp [fixedChainOutputTape, List.append_assoc]

theorem fixedChainOutputTape_cache_eq_of_otherChain
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetChain : ChainIndex) (leafIndices : List LeafIndex)
    (trajectories : List FullChainTrajectory)
    (chains : List ChainIndex) (cache : QueryCache HashSpec)
    (initialOutputs : List HashOutput)
    (result : OutputTrace (AllChainTrajectories × QueryCache HashSpec))
    (hother : targetChain ∉ chains)
    (hresult : result ∈ support
      (outputAllChainTrajectoriesTrace parameter secret cache chains
        initialOutputs)) :
    fixedChainOutputTape parameter targetChain leafIndices trajectories result.1.2 =
      fixedChainOutputTape parameter targetChain leafIndices trajectories cache := by
  induction leafIndices generalizing trajectories with
  | nil => simp [fixedChainOutputTape]
  | cons leafIndex leafIndices ih =>
      cases trajectories with
      | nil => simp [fixedChainOutputTape]
      | cons trajectory trajectories =>
          rw [fixedChainOutputTape, fixedChainOutputTape]
          congr 1
          · apply List.map_congr_left
            intro step _hstep
            unfold chainTrajectoryOutputTable
            rw [outputAllChainTrajectoriesTrace_preserves_other parameter
              secret targetChain leafIndex step (trajectory.get step.castSucc)
                chains cache initialOutputs result hother hresult]
          · exact ih trajectories

noncomputable def allChainOutputTape
    (parameter : PublicParameter) : List ChainIndex → AllChainTrajectories →
      QueryCache HashSpec → List HashOutput
  | [], _, _ => []
  | chain :: chains, trajectories, cache =>
      fixedChainOutputTape parameter chain allLeafIndices (trajectories chain) cache ++
        allChainOutputTape parameter chains trajectories cache

theorem allChainOutputTape_update_of_not_mem
    (parameter : PublicParameter) (chains : List ChainIndex)
    (trajectories : AllChainTrajectories) (updatedChain : ChainIndex)
    (updatedTrajectories : List FullChainTrajectory)
    (cache : QueryCache HashSpec) (hnot : updatedChain ∉ chains) :
    allChainOutputTape parameter chains
        (Function.update trajectories updatedChain updatedTrajectories) cache =
      allChainOutputTape parameter chains trajectories cache := by
  induction chains with
  | nil => rfl
  | cons chain chains ih =>
      have hne : chain ≠ updatedChain := fun heq => hnot (by simp [heq])
      have htail : updatedChain ∉ chains :=
        fun hmem => hnot (by simp [hmem])
      rw [allChainOutputTape, allChainOutputTape,
        Function.update_of_ne hne, ih htail]

theorem outputAllChainTrajectoriesTrace_full_tape
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex), chains.Nodup →
    ∀ (cache : QueryCache HashSpec) (initialOutputs : List HashOutput)
      (result : OutputTrace (AllChainTrajectories × QueryCache HashSpec)),
      result ∈ support
        (outputAllChainTrajectoriesTrace parameter secret cache chains
          initialOutputs) →
      result.2 = initialOutputs ++
        allChainOutputTape parameter chains result.1.1 result.1.2 := by
  intro chains hnodup
  induction chains with
  | nil =>
      intro cache initialOutputs result hresult
      simp only [outputAllChainTrajectoriesTrace, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [allChainOutputTape]
  | cons chain chains ih =>
      intro cache initialOutputs result hresult
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      rw [outputAllChainTrajectoriesTrace, mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      dsimp only [Prod.fst, Prod.snd]
      have hfirstTape :=
        outputFixedSeedChainTrajectoriesTrace_full_tape parameter secret chain
          allLeafIndices allLeafIndices_nodup cache initialOutputs first hfirst
      have hrestTape := ih htail first.1.2 first.2 rest hrest
      have hblock := fixedChainOutputTape_cache_eq_of_otherChain parameter secret
        chain allLeafIndices first.1.1 chains first.1.2 first.2 rest hhead hrest
      rw [hrestTape, hfirstTape, ← hblock]
      rw [allChainOutputTape]
      rw [Function.update_self]
      rw [allChainOutputTape_update_of_not_mem parameter chains rest.1.1 chain
        first.1.1 rest.1.2 hhead]
      simp [List.append_assoc]

noncomputable def globalCachedOutputOfTrajectories
    (parameter : PublicParameter) (trajectories : AllChainTrajectories)
    (cache : QueryCache HashSpec) : GlobalChainEdgeOutputTable := fun edge =>
  (cache (globalChainTableEdgeInput parameter
    (globalChainValueTableOfTrajectories trajectories) edge)).getD 0

noncomputable def fixedCachedOutputOfTrajectories
    (parameter : PublicParameter) (chain : ChainIndex)
    (trajectories : List FullChainTrajectory)
    (cache : QueryCache HashSpec) : LeafIndex × ChainStep → HashOutput := fun edge =>
  (cache (Concrete.CacheView.chainInput parameter edge.1 chain edge.2
    (chainValueTableOfList trajectories
      (edge.1, chainStepDigit edge.2)))).getD 0

theorem fixedChainOutputTape_eq_edgeMap
    (parameter : PublicParameter) (chain : ChainIndex)
    (trajectories : List FullChainTrajectory) (cache : QueryCache HashSpec)
    (hlength : trajectories.length = lifetime) :
    fixedChainOutputTape parameter chain allLeafIndices trajectories cache =
      (allLeafIndices ×ˢ outputChainSteps).map
        (fixedCachedOutputOfTrajectories parameter chain trajectories cache) := by
  let table := chainValueTableOfList trajectories
  have hinverse : listOfChainValueTable table = trajectories :=
    listOfChainValueTable_chainValueTableOfList trajectories hlength
  rw [← hinverse]
  change fixedChainOutputTape parameter chain allLeafIndices
      (allLeafIndices.map fun leafIndex => FullChainTrajectory.ofDigitTable fun digit =>
        table (leafIndex, digit)) cache = _
  have hgeneral : ∀ leafIndices : List LeafIndex,
      fixedChainOutputTape parameter chain leafIndices
          (leafIndices.map fun leafIndex => FullChainTrajectory.ofDigitTable fun digit =>
            table (leafIndex, digit)) cache =
        (leafIndices ×ˢ outputChainSteps).map fun edge =>
          (cache (Concrete.CacheView.chainInput parameter edge.1 chain edge.2
            (table (edge.1, chainStepDigit edge.2)))).getD 0 := by
    intro leafIndices
    induction leafIndices with
    | nil => simp [fixedChainOutputTape]
    | cons leafIndex leafIndices ih =>
        rw [List.map_cons, fixedChainOutputTape, List.product_cons,
          List.map_append, ih]
        congr 1
  rw [hgeneral allLeafIndices]
  apply List.map_congr_left
  rintro ⟨leafIndex, step⟩ _hedge
  simp only [fixedCachedOutputOfTrajectories]
  rw [hinverse]

theorem allChainOutputTape_eq_edgeMap
    (parameter : PublicParameter) (trajectories : AllChainTrajectories)
    (cache : QueryCache HashSpec)
    (hlength : ∀ chain, (trajectories chain).length = lifetime) :
    allChainOutputTape parameter allChains trajectories cache =
      globalOutputEdgeOrder.map
        (globalCachedOutputOfTrajectories parameter trajectories cache) := by
  unfold globalOutputEdgeOrder
  have hgeneral : ∀ chains : List ChainIndex,
      allChainOutputTape parameter chains trajectories cache =
        (chains ×ˢ (allLeafIndices ×ˢ outputChainSteps)).map
          (globalCachedOutputOfTrajectories parameter trajectories cache) := by
    intro chains
    induction chains with
    | nil => simp [allChainOutputTape]
    | cons chain chains ih =>
        rw [allChainOutputTape, List.product_cons, List.map_append, ih]
        rw [fixedChainOutputTape_eq_edgeMap parameter chain
          (trajectories chain) cache (hlength chain)]
        rw [List.map_map]
        congr 1
  exact hgeneral allChains

theorem outputGlobalChainTrajectoryMaterialTrace_material_support
    (parameter : PublicParameter)
    (trace : OutputTrace GlobalChainTrajectoryMaterial)
    (htrace : trace ∈ support
      (outputGlobalChainTrajectoryMaterialTrace parameter)) :
    trace.1 ∈ support (outputGlobalChainTrajectoryMaterial parameter) := by
  have hmapped : trace.1 ∈ support
      (Prod.fst <$> outputGlobalChainTrajectoryMaterialTrace parameter) := by
    rw [support_map]
    exact ⟨trace, htrace, rfl⟩
  rw [outputGlobalChainTrajectoryMaterialTrace_fst parameter] at hmapped
  exact hmapped

theorem outputGlobalChainTrajectoryMaterialTrace_full_tape
    (parameter : PublicParameter)
    (trace : OutputTrace GlobalChainTrajectoryMaterial)
    (htrace : trace ∈ support
      (outputGlobalChainTrajectoryMaterialTrace parameter)) :
    trace.2 = allChainOutputTape parameter allChains trace.1.2.1
      trace.1.2.2 := by
  rw [outputGlobalChainTrajectoryMaterialTrace,
    mem_support_bind_iff] at htrace
  obtain ⟨secret, _hsecret, htrace⟩ := htrace
  rw [mem_support_bind_iff] at htrace
  obtain ⟨trajectories, htrajectories, hpure⟩ := htrace
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst trace
  simpa using outputAllChainTrajectoriesTrace_full_tape parameter secret
    allChains allChains_nodup ∅ [] trajectories htrajectories

theorem globalChainEdgeOutputTableOfOutputTrace_eq_cached
    (parameter : PublicParameter)
    (trace : OutputTrace GlobalChainTrajectoryMaterial)
    (htrace : trace ∈ support
      (outputGlobalChainTrajectoryMaterialTrace parameter)) :
    globalChainEdgeOutputTableOfOutputTape trace.2 =
      globalCachedOutputOfTrajectories parameter trace.1.2.1 trace.1.2.2 := by
  have hmaterial :=
    outputGlobalChainTrajectoryMaterialTrace_material_support parameter trace
      htrace
  have hactual := outputGlobalChainTrajectoryMaterial_support_as_actual
    parameter trace.1 hmaterial
  have hinfo := Concrete.allChainTrajectoriesFromCache_support_info parameter
    trace.1.1 allChains ∅ trace.1.2 allChains_nodup hactual
  have hlength : ∀ chain, (trace.1.2.1 chain).length = lifetime := by
    intro chain
    exact (hinfo.2 chain (mem_allChains chain)).1
  rw [outputGlobalChainTrajectoryMaterialTrace_full_tape parameter trace htrace,
    allChainOutputTape_eq_edgeMap parameter trace.1.2.1 trace.1.2.2 hlength,
    globalChainEdgeOutputTableOfOutputTape_map]


end XmssSecurity.CappedChain
