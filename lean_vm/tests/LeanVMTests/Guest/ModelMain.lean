import LeanVM.Guest.EndKnowB

/-!
# Tests: `main` and the guest's end theorem over a hash model (W2, Main + End)

* The generic lemmas of `B1/Main/*M.lean`, `Located/*B.lean`, `Located/InterfaceM.lean`,
  `Located/MainB.lean` and `Guest/EndKnowB.lean` rest on Lean's three axioms; among them T2,
  `End.guest_knowledge_model`.
* **At the deployed model the end theorem is the deployed one**: `guest_knowledge_of_model`
  (`GuestKnowledge guest decode` from `guest_knowledge_model` at `HashModel.deployed`, every open
  callee its deployed lemma by `guestHypsM_deployed`, the decoder `decode` by `decodeB_deployed`).
* The transfers' freeness, by the kernel.
-/

namespace LeanVMTests.Guest.ModelMain

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Node

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.B1.Main.signers_compress_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.signers_compress_model

/-- info: 'LeanVM.Guest.B1.Main.unfoldsB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.unfoldsB_deployed

/-- info: 'LeanVM.Guest.B1.Main.loop3_step_wM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop3_step_wM

/-- info: 'LeanVM.Guest.B1.Main.loop4_step_wM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop4_step_wM

/-- info: 'LeanVM.Guest.B1.Main.loop100_stepCM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop100_stepCM

/-- info: 'LeanVM.Guest.B1.Main.loop5_step_wM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop5_step_wM

/-- info: 'LeanVM.Guest.B1.Main.writers_good_wM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.writers_good_wM

/-- info: 'LeanVM.Guest.B1.Main.childClaimsWith_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.childClaimsWith_of

/-- info: 'LeanVM.Guest.B1.Main.main_sound_wM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.main_sound_wM

/-- info: 'LeanVM.Guest.B1.Main.obsChain_soundM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.obsChain_soundM

/-- info: 'LeanVM.Guest.B1.Main.loop95_stepM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop95_stepM

/-- info: 'LeanVM.Guest.B1.Main.loop96_stepM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop96_stepM

/-- info: 'LeanVM.Guest.B1.Main.loop98_stepM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop98_stepM

/-- info: 'LeanVM.Guest.B1.Main.loop97_stepB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop97_stepB

/-- info: 'LeanVM.Guest.B1.Main.loop99_stepB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop99_stepB

/-- info: 'LeanVM.Guest.B1.Main.batchRoundsWith_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.batchRoundsWith_length

/-- info: 'LeanVM.Guest.B1.Main.batchWith_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.batchWith_of

/-- info: 'LeanVM.Guest.B1.Main.aggSeedD_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.aggSeedD_eq

/-- info: 'LeanVM.Guest.B1.Main.meaningBatchSumcheckM_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.meaningBatchSumcheckM_deployed

/-- info: 'LeanVM.Guest.B1.Main.batchSumcheckM_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.batchSumcheckM_deployed

/-- info: 'LeanVM.Guest.B1.Main.aggregate_claims_sound_wM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.aggregate_claims_sound_wM

/-- info: 'LeanVM.Guest.B1.Main.statement_digest_soundM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.statement_digest_soundM

/-- info: 'LeanVM.Guest.B1.Main.claim_list_digest_soundM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.claim_list_digest_soundM

/-- info: 'LeanVM.Guest.B1.Main.child_claim_list_digest_soundM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.child_claim_list_digest_soundM

/-- info: 'LeanVM.Guest.B1.Main.da_list_digest_soundM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.da_list_digest_soundM

/-- info: 'LeanVM.Guest.B1.Main.cover_da_root_soundM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.cover_da_root_soundM

/-- info: 'LeanVM.Guest.B1.Main.exponent_tables_soundM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.exponent_tables_soundM

/-- info: 'LeanVM.Guest.Located.frameOfB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.frameOfB_deployed

/-- info: 'LeanVM.Guest.Located.bodyAt_frameOfB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.bodyAt_frameOfB

/-- info: 'LeanVM.Guest.Located.frameOfB_of_bodyAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.frameOfB_of_bodyAt

/-- info: 'LeanVM.Guest.Located.loopDecB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.loopDecB_spec

/-- info: 'LeanVM.Guest.Located.wDaLB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.wDaLB_deployed

/-- info: 'LeanVM.Guest.Located.daWit_outM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.daWit_outM

/-- info: 'LeanVM.Guest.Located.xmssWitB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.xmssWitB_deployed

/-- info: 'LeanVM.Guest.Located.sphincsWitB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.sphincsWitB_deployed

/-- info: 'LeanVM.Guest.Located.xmssWit_outM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.xmssWit_outM

/-- info: 'LeanVM.Guest.Located.fkWit_soundM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.fkWit_soundM

/-- info: 'LeanVM.Guest.Located.sphincsWit_outM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.sphincsWit_outM

/-- info: 'LeanVM.Guest.Located.wOLB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.wOLB_deployed

/-- info: 'LeanVM.Guest.Located.wVsLB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.wVsLB_deployed

/-- info: 'LeanVM.Guest.Located.wOLB_spec_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.wOLB_spec_deployed

/-- info: 'LeanVM.Guest.Located.vsWit_outM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.vsWit_outM

/-- info: 'LeanVM.Guest.Located.guestHypsM_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.guestHypsM_deployed

/-- info: 'LeanVM.Guest.Located.wAL_outM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.wAL_outM

/-- info: 'LeanVM.Guest.Located.calleesWM_located' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.calleesWM_located

/-- info: 'LeanVM.Guest.End.decodeB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.decodeB_deployed

/-- info: 'LeanVM.Guest.End.guest_knowledge_model_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.guest_knowledge_model_at

/-- info: 'LeanVM.Guest.End.guest_knowledge_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.guest_knowledge_model

/-- info: 'LeanVM.Guest.End.nodeRelWith_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.nodeRelWith_deployed

/-- info: 'LeanVM.Guest.End.decodesOnWith_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.decodesOnWith_deployed

/-- info: 'LeanVM.Guest.End.guest_knowledge_of_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.guest_knowledge_of_model

/-! ## At the deployed model -/

/-- **T2 at the deployed model is `guest_knowledge`'s statement.** -/
example : GuestKnowledge LeanVM.Guest.guest End.decode := End.guest_knowledge_of_model

/-- **T2's statement, at every hash model with its open callees.** -/
example (M : HashModel) (H : Located.GuestHypsM M) (input : PublicInput) (t : Trace LeanVM.Guest.guest)
    (hv : ValidExecutionB M.sem LeanVM.Guest.guest input t) :
    statementDigestWith M.H (End.decodeB M.sem t.image).seed (End.decodeB M.sem t.image).statement =
        some (LeanVM.publicDigest input) ∧
      NodeRelWith M.H B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow (LeanVM.bytecodeWords LeanVM.Guest.guest)
        (End.decodeB M.sem t.image).seed (End.decodeB M.sem t.image).statement
        (End.decodeB M.sem t.image).witness :=
  End.guest_knowledge_model M H input t hv

/-- **T2's statement at any named frames** (decision E2E-5), the decoder V_I runs. -/
example (M : HashModel) (H : Located.GuestHypsM M) (fr : String → List E → Option ℕ)
    (input : PublicInput) (t : Trace LeanVM.Guest.guest)
    (hv : ValidExecutionB M.sem LeanVM.Guest.guest input t) :
    statementDigestWith M.H (End.decodeAt M.sem fr t.image).seed
        (End.decodeAt M.sem fr t.image).statement = some (LeanVM.publicDigest input) ∧
      NodeRelWith M.H B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow (LeanVM.bytecodeWords LeanVM.Guest.guest)
        (End.decodeAt M.sem fr t.image).seed (End.decodeAt M.sem fr t.image).statement
        (End.decodeAt M.sem fr t.image).witness :=
  End.guest_knowledge_model_at M H fr input t hv

/-- The baked start is the label's hash at BLAKE2s. -/
example : B1.Main.aggSeedD = LeanVM.Protocol.Blake2sHash.blake2sBytes batchLabel :=
  B1.Main.aggSeedD_eq

/-! ## The transfers, by the kernel -/

example : coreProgram.FreeOn ["__loop97"] = true := B1.Main.freeOn_loop97

example : coreProgram.FreeOn ["__loop99"] = true := B1.Main.freeOn_loop99

example : coreProgram.FreeOn ["cover_da_root"] = true := B1.Main.freeOn_cover_da_root

/-- `__loop95` hashes: it is not free. -/
example : coreProgram.FreeOn ["__loop95"] = false := by decide +kernel

end LeanVMTests.Guest.ModelMain
