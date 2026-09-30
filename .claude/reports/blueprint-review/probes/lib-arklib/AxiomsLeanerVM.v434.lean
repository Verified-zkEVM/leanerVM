import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput

/-! Probe B1: `#print axioms` of leanerVM's master theorems, phases and composition. -/

open LeanerVM.Protocol

#print axioms LeanerVM.Protocol.piop_perfectCompleteness
#print axioms LeanerVM.Protocol.piop_rbrKnowledgeSoundness
#print axioms LeanerVM.Protocol.piop_rbrKnowledgeSoundness_exists
#print axioms LeanerVM.Protocol.commitSecurity
#print axioms LeanerVM.Protocol.commitComplete
#print axioms LeanerVM.Protocol.publicInputSecurity
#print axioms LeanerVM.Protocol.publicInputComplete
#print axioms LeanerVM.Protocol.Component.Security.append
#print axioms LeanerVM.Protocol.Component.Complete.append
#print axioms LeanerVM.Protocol.Verifier.KnowledgeStateFunction.appendGuarded
#print axioms LeanerVM.Protocol.Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
#print axioms LeanerVM.Protocol.piopExtractor
#print axioms LeanerVM.Protocol.commitExtractor
#print axioms LeanerVM.Protocol.PublicInput.extractor
#print axioms LeanerVM.Protocol.Component.sendExtractor
#print axioms LeanerVM.Protocol.Phases.Security.toDef
#print axioms LeanerVM.Protocol.Phases.Complete.toDef
