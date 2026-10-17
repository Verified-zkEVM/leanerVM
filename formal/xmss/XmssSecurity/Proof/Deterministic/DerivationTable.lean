import XmssSecurity.Proof.Seeded.KeygenExpansion
import XmssSecurity.Proof.Seeded.FiniteTable
import XmssSecurity.Proof.Seeded.CacheCoupling

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def signRequestEquiv : SignRequest ≃ (LeafIndex × Message) where
  toFun request := (request.leafIndex, request.message)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype SignRequest := Fintype.ofEquiv (LeafIndex × Message) signRequestEquiv.symm

abbrev RandomizerPosition := SignRequest × BitVec 32
abbrev RandomizerOutputs := RandomizerPosition → HashOutput

noncomputable opaque randomizerOutputsSampleableType : SampleableType RandomizerOutputs :=
  SampleableType.ofFintype RandomizerOutputs

noncomputable local instance : SampleableType RandomizerOutputs := randomizerOutputsSampleableType

noncomputable def sampleRandomizerOutputs : ProbComp RandomizerOutputs := $ᵗ RandomizerOutputs

def randomizerInputs (parameter : PublicParameter) (seed : MasterSeed) (position : RandomizerPosition) : HashInput :=
  randomizerHashInput parameter seed position.1.leafIndex position.1.message position.2

theorem randomizerInputs_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (randomizerInputs parameter seed) := by
  intro left right h
  have heq := randomizerHashInput_injective h
  apply Prod.ext
  · cases left with
    | mk left trial =>
      cases right with
      | mk right other =>
        cases left
        cases right
        simp_all
  · exact heq.2.2.2.2

theorem derivationCache_randomizer_fresh (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : ChainOutputs) (position : RandomizerPosition) :
    derivationCache seed parameterOutput outputs
      (randomizerInputs (truncateHash parameterOutput) seed position) = none := by
  have hchain : ∀ leafIndex chain,
      randomizerInputs (truncateHash parameterOutput) seed position ≠
        chainInputs (truncateHash parameterOutput) seed leafIndex chain := fun leafIndex chain =>
    randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ _ (.chain leafIndex chain)
  rw [derivationCache, cacheRows_apply_of_not_mem _ _ _ _ hchain, parameterCache]
  exact (QueryCache.cacheQuery_of_ne (spec := HashSpec) ∅ _
    (randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ _ .parameter)).trans
      (QueryCache.empty_apply _)

noncomputable def signingDerivationCache (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : ChainOutputs) (randomizers : RandomizerOutputs) : QueryCache HashSpec :=
  cacheTable (derivationCache seed parameterOutput outputs)
    (randomizerInputs (truncateHash parameterOutput) seed) randomizers

theorem signingDerivationCache_randomizer (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : ChainOutputs) (randomizers : RandomizerOutputs) (position : RandomizerPosition) :
    signingDerivationCache seed parameterOutput outputs randomizers
      (randomizerInputs (truncateHash parameterOutput) seed position) = some (randomizers position) := by
  rw [signingDerivationCache]
  exact cacheTable_apply _ _ (randomizerInputs_injective _ _) _ _

theorem signingDerivationCache_agreeOutside (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : ChainOutputs) (randomizers : RandomizerOutputs) :
    AgreeOutside (fun input => SeedHit input seed)
      (signingDerivationCache seed parameterOutput outputs randomizers) ∅ := by
  intro input hinput
  have hrandomizer : ∀ position, input ≠ randomizerInputs (truncateHash parameterOutput) seed position := by
    rintro position rfl
    exact hinput (derivationSeedHit_randomizer (truncateHash parameterOutput) seed position.1.leafIndex
      position.1.message position.2)
  rw [signingDerivationCache, cacheTable_apply_of_not_mem _ _ _ _ hrandomizer,
    derivationCache_of_not_seedHit seed parameterOutput outputs input hinput]
  exact (QueryCache.empty_apply _).symm

noncomputable def prepareRandomizers (parameter : PublicParameter) (seed : MasterSeed) :
    OracleComp HashSpec RandomizerOutputs := queryTable (randomizerInputs parameter seed)

theorem evalDist_prepareRandomizers (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : ChainOutputs) :
    𝒮[(simulateQ randomOracle (prepareRandomizers (truncateHash parameterOutput) seed)).run
      (derivationCache seed parameterOutput outputs)] =
        𝒮[(fun randomizers => (randomizers, signingDerivationCache seed parameterOutput outputs randomizers)) <$>
          sampleRandomizerOutputs] :=
  evalDist_queryTable_fresh _ (randomizerInputs_injective _ seed) _
    (derivationCache_randomizer_fresh seed parameterOutput outputs)

end XmssSecurity.Seeded
