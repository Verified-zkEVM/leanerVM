import SphincsFors.SecurityGraphCountedSigner

/-! The counted graph signer composed through an arbitrary adaptive adversary and the actual
verifier: explicit-reveal cost programs for the interaction, the rest of the game and the whole
game, which retain the strong signing log, and the cost of key generation on a fixed answer
function. -/

open OracleComp OracleSpec
namespace SphincsFors.Security.GraphView
open Concrete Completeness Prefix HiddenGraph SeedCoupling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] signCostSource Randomized.sign Seeded.keygenFromSeed

def ordinaryCostSource : QueryImpl OracleWorld (OracleComp CostSpec)
  | .inl request => liftM (CostSpec.query (.inl (.inl request)))
  | .inr request => liftM (CostSpec.query (.inl (.inr (.inl request))))

variable [Params]

noncomputable def costInteraction (parameter : PublicParameter) (data : PublicData) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) :=
  ordinaryCostSource.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) +
    QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
      (fun message => signCostSource parameter data message)

noncomputable def costRest (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpec Bool := do
  let pk : PublicKey := ⟨data.root, parameter⟩
  let (forgery, log) ← (simulateQ (costInteraction parameter data) (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def costGame (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpec Bool := do
  HiddenCost.tick (226 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight))
  costRest parameter data adversary

end SphincsFors.Security.GraphView
