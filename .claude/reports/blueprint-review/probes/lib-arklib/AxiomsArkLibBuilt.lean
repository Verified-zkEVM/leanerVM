import LeanerVM.Protocol.Spine.Compose
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.GuardedNary
import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
import ArkLib.OracleReduction.Composition.Sequential.Append.RoundByRound
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-! Probe B2: `#print axioms` of the ArkLib declarations the blueprint cites, for the modules
that leanerVM's build contains (ArkLib at the pin `dca90385`). -/

-- definitions
#print axioms Reduction.completeness
#print axioms Reduction.perfectCompleteness
#print axioms OracleReduction.perfectCompleteness
#print axioms Verifier.soundness
#print axioms Verifier.knowledgeSoundness
#print axioms Extractor.Straightline
#print axioms Verifier.StateFunction
#print axioms Verifier.KnowledgeStateFunction
#print axioms Extractor.RoundByRound
#print axioms Verifier.rbrSoundness
#print axioms Verifier.rbrKnowledgeSoundness
#print axioms Verifier.rbrKnowledgeSoundnessWorstCase
#print axioms Verifier.rbrKnowledgeSoundnessWorstCaseWith
#print axioms Verifier.GuardedForm
#print axioms Prover.OutputIsPure
#print axioms OracleVerifier.toVerifier
#print axioms OracleReduction.append
#print axioms OracleReduction.seqCompose
#print axioms ProtocolSpec.seqCompose
#print axioms Extractor.RoundByRound.append
#print axioms Verifier.StateFunction.append
#print axioms Verifier.GuardedForm.append
-- proved theorems
#print axioms Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
#print axioms Verifier.rbrSoundnessWorstCase_implies_rbrSoundness
#print axioms Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith
#print axioms ProtocolSpec.probEvent_simulateQ_addLift_getChallenge_bind_le
#print axioms Reduction.perfectCompleteness_of_run_support
#print axioms OracleReduction.append_perfectCompleteness_of_pure_verifiers
#print axioms OracleReduction.append_perfectCompleteness_of_guarded_verifiers
#print axioms OracleReduction.append_completeness_of_guarded_verifiers
#print axioms OracleReduction.seqCompose_completeness_of_guarded_verifiers
#print axioms OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
#print axioms Reduction.seqCompose_completeness_of_guarded_verifiers
#print axioms Reduction.append_completeness_of_guarded_verifiers
#print axioms Reduction.append_completeness_of_guarded_prover_factorization
#print axioms Verifier.append_rbrSoundnessWorstCase_of_pure_first
#print axioms Prover.OutputIsPure.append
#print axioms OracleVerifier.append_toVerifier
#print axioms MvPolynomial.schwartz_zippel_counting
#print axioms prob_eval_zero_le_div
#print axioms MvPolynomial.prob_eval_zero_le_div
-- admitted at the pin
#print axioms Verifier.append_soundness
#print axioms Verifier.append_knowledgeSoundness
#print axioms Verifier.append_rbrSoundness
#print axioms Verifier.append_rbrKnowledgeSoundness
#print axioms OracleVerifier.append_rbrKnowledgeSoundness
#print axioms Verifier.seqCompose_soundness
#print axioms Verifier.seqCompose_knowledgeSoundness
#print axioms Verifier.seqCompose_rbrSoundness
#print axioms Verifier.seqCompose_rbrKnowledgeSoundness
#print axioms OracleVerifier.seqCompose_rbrKnowledgeSoundness
#print axioms OracleVerifier.numQueries
