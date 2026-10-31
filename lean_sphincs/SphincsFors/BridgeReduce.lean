import SphincsFors.BridgeStop
import SphincsFors.SecurityHiddenCost
import SphincsFors.SecuritySeedGuess

/-! The seed-free, budget-capped graph-view game: the canonical graph cache and answer function of
a sample without any seed-addressed entry, the seed-free run and experiment averaged over
independent material, graph labels and remaining answers, and its win event. `BridgeDet` bounds
the SUF-CMA advantage of the deterministic signer by this game plus the cost of naming the seed. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.Reduce

open Completeness SeedCoupling Internalize Eager Short SeedModel Graph Assembly Stop HiddenCost
  GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem programGraphCache_congr_base (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (positions : List Position)
    (labels : CanonicalGraphLabels) (base base' : QueryCache HashSpec) (input : HashInput)
    (h : base input = base' input) :
    programGraphCache parameter otsSecret ftsSecret positions labels base input =
      programGraphCache parameter otsSecret ftsSecret positions labels base' input := by
  induction positions generalizing base base' with
  | nil => exact h
  | cons first rest ih =>
      apply ih
      by_cases heq : input = canonicalGraphInput parameter otsSecret ftsSecret first labels
      · subst heq
        show (base.cacheQuery _ _) _ = (base'.cacheQuery _ _) _
        simp [QueryCache.cacheQuery_self]
      · show (base.cacheQuery _ _) input = (base'.cacheQuery _ _) input
        rw [QueryCache.cacheQuery_of_ne _ _ heq, QueryCache.cacheQuery_of_ne _ _ heq]
        exact h

noncomputable local instance reduceLabelsSampleable : SampleableType CanonicalGraphLabels :=
  graphLabelsSampleable

variable [Params]

/-- The canonical graph cache without any seed-addressed entry. -/
noncomputable def graphCache (material : Material) (answers : CanonicalGraphLabels) :
    QueryCache HashSpec :=
  programGraphCache (parameter material) (GraphCorrectness.materialOts material)
    (GraphCorrectness.materialFts material) (graphOrder (PrunedGraph.active (parameter material)))
    (labelsOf material answers) ∅

noncomputable def graphFn (material : Material) (answers : CanonicalGraphLabels) (table : Eager.Table) :
    HashInput → HashOutput :=
  extend (graphCache material answers) table

noncomputable def graphCoordinates (material : Material) (answers : CanonicalGraphLabels) :
    HiddenGraph.Table :=
  HiddenGraph.coordinates (GraphCorrectness.materialOts material) (GraphCorrectness.materialFts material)
    (labelsOf material answers)

theorem sampleFn_agree (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) (input : HashInput) (hnot : ¬SeedGuess.SeedHit input seed) :
    sampleFn material seed answers table input = graphFn material answers table input := by
  simp only [sampleFn, graphFn, extend, preparedCache, graphCache]
  rw [programGraphCache_congr_base _ _ _ _ _ _ ∅ input (programCache_agreeOutside ∅ seed material input hnot)]

theorem sampleCoordinates_eq (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) :
    sampleCoordinates material seed answers table = graphCoordinates material answers := by
  rw [sampleCoordinates, graphCoordinates,
    ← GraphCorrectness.materialOts_eq _ seed material (sample_agreement material seed answers table),
    ← GraphCorrectness.materialFts_eq _ seed material (sample_agreement material seed answers table)]

/-- One seed-free capped graph-view run. -/
noncomputable def seedFreeRun (adversary : Adversary) (q : Nat) (material : Material)
    (answers : CanonicalGraphLabels) (table : Eager.Table) :
    ProbComp (Option Bool × List (Entry HashInput)) :=
  costRun (graphFn material answers table) (graphCoordinates material answers)
    (cap (costGame (parameter material) (publicData (labelsOf material answers)) adversary) q)

noncomputable def seedFreeExperiment (adversary : Adversary) (q : Nat) :
    ProbComp (Option Bool × List (Entry HashInput)) := do
  let material ← sampleMaterial
  let answers ← $ᵗ CanonicalGraphLabels
  let table ← $ᵗ Eager.Table
  seedFreeRun adversary q material answers table

def Win (result : Option Bool × List (Entry HashInput)) : Prop :=
  ∃ value, result.1 = some value ∧ value = true

end SphincsFors.Security.Reduce
