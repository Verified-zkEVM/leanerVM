import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.ToArkLib.Refinement
import LeanerVM.Protocol.PublicInput

/-!
Probe P1 (code-spine): axioms and computability of the spine's load-bearing declarations.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

#print axioms piop_perfectCompleteness
#print axioms piop_rbrKnowledgeSoundness
#print axioms piop_rbrKnowledgeSoundness_exists
#print axioms piopExtractor
#print axioms commitExtractor
#print axioms Component.sendExtractor
#print axioms commitSecurity
#print axioms commitComplete
#print axioms Component.Security.append
#print axioms Component.Complete.append
#print axioms Phases.Security.toDef
#print axioms M3Holds
#print axioms Component.passThroughSecurity
#print axioms publicInputSecurity
#print axioms Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
#print axioms Verifier.KnowledgeStateFunction.appendGuarded
#print axioms Extractor.RoundByRound.append
#print axioms Refinement.map_option_valid
#print axioms Toy.read_eval

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for n in [``piopExtractor, ``commitExtractor, ``Component.sendExtractor,
      ``Phases.Security.toDef, ``Phases.Complete.toDef, ``Component.Security.append,
      ``Component.Complete.append, ``Extractor.RoundByRound.append, ``leanVmPiop,
      ``leanVmVerifier, ``leanVmProver, ``piopError, ``Phases.toDef, ``Component.Def.append,
      ``commitDef, ``Component.sendOracle, ``Component.sendProver, ``Component.sendVerifier,
      ``publicInputPhase, ``publicInputSecurity, ``publicInputComplete, ``commitSecurity,
      ``commitComplete, ``Component.passThrough, ``Component.passThroughSecurity,
      ``Component.passThroughExtractor, ``PublicInput.extractor, ``PublicInput.prover,
      ``PublicInput.verifier, ``Verifier.KnowledgeStateFunction.appendGuarded,
      ``Component.guardedAppend, ``M3Holds, ``Toy.toy, ``Toy.honest,
      ``Extractor.Straightline.map, ``OracleReduction.append] do
    logInfo m!"{n}: noncomputable={Lean.isNoncomputable env n}"
