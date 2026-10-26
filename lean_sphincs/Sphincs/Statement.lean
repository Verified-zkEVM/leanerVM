module

public import Sphincs.Randomized
public import VCVio.OracleComp.QueryTracking.WriterCost
public import Sphincs.Layered

/-!
The SUF-CMA experiment, adapted from leanVM b7a107256 to pruning: forgeries, signing transcripts and
their tests, adversaries, and the counted experiment with the randomized signer (genuinely random
randomizers), keyed by a uniform scheme seed. All hash calls in the experiment count, including
repeated calls and honest-party calls. The security target, for the deterministic signer and key
generation from the key's seed, is in `StatementDet`.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsLayered

@[expose] public section

variable [Params]

namespace Security

structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

noncomputable def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => liftM (Randomized.sign sk request)

noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromMaster seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

end Security

end

end SphincsLayered
