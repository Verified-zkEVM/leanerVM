import LeanVM.Guest.B1.Sumcheck
import LeanVM.Guest.B1.Grind
import LeanVM.Guest.B1.Exponent
import LeanVM.Guest.B1.FoldFinal
import LeanVM.Guest.B1.Loops
import LeanVM.Guest.B1.QueryBits
import LeanVM.Guest.B1.RowWeights
import LeanVM.Guest.B1.Log2
import LeanVM.Guest.B1.Whir.StackedM
import LeanVM.Guest.Located.RootWhirM

/-!
# Tests: the B1 root and WHIR soundness lemmas under a hash model (W2, agent 1)

* The generic lemmas of the B1 root (`sumcheck_round4/5`, `opening_fold`, `opening_final_message`,
  `batch_sumcheck`, `opening_ood_point`, `grind_check`, the hash-free transfers) and of the WHIR
  opening (`verify_merkle_cap`, `opening_queries`, `Compile.openAll` over `M.H`, `open_stacked`,
  `SoundOpenM`) rest on Lean's three axioms.
* **At the deployed model they are the deployed ones**: `SoundOpenM` at `HashModel.deployed` gives
  `SoundOpen`.
-/

namespace LeanVMTests.Guest.ModelRootWhir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.B1.sumcheck_round4_modelD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sumcheck_round4_modelD

/-- info: 'LeanVM.Guest.B1.sumcheck_round5_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sumcheck_round5_model

/-- info: 'LeanVM.Guest.B1.sumcheck_round5_modelD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sumcheck_round5_modelD

/-- info: 'LeanVM.Guest.B1.opening_fold_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_fold_model

/-- info: 'LeanVM.Guest.B1.opening_fold_modelD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_fold_modelD

/-- info: 'LeanVM.Guest.B1.assert_canonical_iffB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.assert_canonical_iffB

/-- info: 'LeanVM.Guest.B1.opening_final_message_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_final_message_model

/-- info: 'LeanVM.Guest.B1.opening_final_message_L4_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_final_message_L4_model

/-- info: 'LeanVM.Guest.B1.opening_final_message_L8_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_final_message_L8_model

/-- info: 'LeanVM.Guest.B1.opening_final_message_L16_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_final_message_L16_model

/-- info: 'LeanVM.Guest.B1.opening_final_message_L32_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_final_message_L32_model

/-- info: 'LeanVM.Guest.B1.batch_sumcheck_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.batch_sumcheck_model

/-- info: 'LeanVM.Guest.B1.batch_sumcheck_L22_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.batch_sumcheck_L22_model

/-- info: 'LeanVM.Guest.B1.batch_sumcheck_L28_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.batch_sumcheck_L28_model

/-- info: 'LeanVM.Guest.B1.batchRoundsWith_cons_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.batchRoundsWith_cons_run

/-- info: 'LeanVM.Guest.B1.meaningBatchSumcheckWith_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.meaningBatchSumcheckWith_deployed

/-- info: 'LeanVM.Guest.B1.opening_ood_point_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_ood_point_model

/-- info: 'LeanVM.Guest.B1.meaningOpeningOodPointWith_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.meaningOpeningOodPointWith_deployed

/-- info: 'LeanVM.Guest.B1.grind_check_rel_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.grind_check_rel_model

/-- info: 'LeanVM.Guest.B1.meaningGrindCheckWith_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.meaningGrindCheckWith_deployed

/-- info: 'LeanVM.Guest.B1.g_power_of_word_L6_iffB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.g_power_of_word_L6_iffB

/-- info: 'LeanVM.Guest.B1.fold_final_msg_L5_iffB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.fold_final_msg_L5_iffB

/-- info: 'LeanVM.Guest.B1.eq_prefix_chain_iffB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.eq_prefix_chain_iffB

/-- info: 'LeanVM.Guest.B1.rs_eq_run_iffB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.rs_eq_run_iffB

/-- info: 'LeanVM.Guest.B1.decode_query_bits_L20_iffB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.decode_query_bits_L20_iffB

/-- info: 'LeanVM.Guest.B1.opening_row_weights_L6_L1_iffB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_row_weights_L6_L1_iffB

/-- info: 'LeanVM.Guest.B1.verify_log2_ceil_L15_L34_iffB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_log2_ceil_L15_L34_iffB

/-- info: 'LeanVM.Guest.B1.log2_ceil_in_the_exponent_L15_L34_iffB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.log2_ceil_in_the_exponent_L15_L34_iffB

/-- info: 'LeanVM.Guest.B1.holdsListB_iff_of_noBlake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.holdsListB_iff_of_noBlake

/-- info: 'LeanVM.Guest.B1.loopB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.loopB_sound

/-- info: 'LeanVM.Guest.B1.guarded_loopB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.guarded_loopB_sound

/-- info: 'LeanVM.Guest.B1.verify_merkle_cap_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_merkle_cap_model

/-- info: 'LeanVM.Guest.B1.verify_merkle_cap_L8_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_merkle_cap_L8_model

/-- info: 'LeanVM.Guest.B1.cap_climbM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.cap_climbM

/-- info: 'LeanVM.Guest.B1.meaningVerifyMerkleCapWith_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.meaningVerifyMerkleCapWith_deployed

/-- info: 'LeanVM.Guest.B1.opening_queries_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_queries_model

/-- info: 'LeanVM.Guest.B1.opening_queries_L1_L64_L8_L26_L6_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_queries_L1_L64_L8_L26_L6_model

/-- info: 'LeanVM.Guest.B1.os_openAll_ofM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_openAll_ofM

/-- info: 'LeanVM.Guest.B1.sqAllM_of_runsToM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sqAllM_of_runsToM

/-- info: 'LeanVM.Guest.B1.os_runsToM_sampleQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_runsToM_sampleQueries

/-- info: 'LeanVM.Guest.B1.runsToM_grindP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.runsToM_grindP

/-- info: 'LeanVM.Guest.B1.open_stacked_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.open_stacked_model

/-- info: 'LeanVM.Guest.B1.open_stacked_L27_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.open_stacked_L27_model

/-- info: 'LeanVM.Guest.B1.soundOpenM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.soundOpenM

/-- info: 'LeanVM.Guest.B1.open_stacked_frame_wCM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.open_stacked_frame_wCM

/-- info: 'LeanVM.Guest.B1.opening_queries_frame_wM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_queries_frame_wM

/-- info: 'LeanVM.Guest.B1.oqLoop_frame_wM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqLoop_frame_wM

/-- info: 'LeanVM.Guest.B1.oqOpeningOf_okM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqOpeningOf_okM

/-- info: 'LeanVM.Guest.B1.exists_soundQueriesWM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.exists_soundQueriesWM

/-- info: 'LeanVM.Guest.Located.batchSumcheckM_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.batchSumcheckM_model

/-- info: 'LeanVM.Guest.Located.openStacked_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Located.openStacked_model

/-! ## The `GuestHypsM` fields -/

set_option maxRecDepth 100000 in
/-- The B1 root's two fields of `Located.GuestHypsM` have the field's types. -/
example (M : HashModel) : (∀ rd, Main.MemOk rd → Main.BatchSumcheckM M rd) ∧
    ∀ (fr : String → List E → Option ℕ) {κ : ℕ} (L : MemImage κ), 16 ≤ κ → κ ≤ 32 →
      VerifySub.SoundOpenWCM M L.read (Check.RLB M.sem coreProgram L certByName)
        (Located.wOLB M.sem fr L) :=
  ⟨Located.batchSumcheckM_model M, fun fr {_} L h1 h2 => Located.openStacked_model M fr L h1 h2⟩

/-! ## The deployed instance -/

/-- `open_stacked`'s generic soundness at the deployed model is the deployed `SoundOpen`. -/
example (rd : Reader) : VerifySub.SoundOpen rd :=
  VerifySub.soundOpenM_deployed.mp (soundOpenM HashModel.deployed rd)

/-- `batch_sumcheck__L22`'s generic soundness at the deployed model gives the deployed meaning. -/
example (rd : Reader) (args rets : List E) (h : coreProgram.Rel rd "batch_sumcheck__L22" args rets) :
    MeaningBatchSumcheck 22 rd args rets := by
  rw [← relB_deployed] at h
  exact (meaningBatchSumcheckWith_deployed 22 rd args rets).mp (batch_sumcheck_L22_model rd args rets h)

end LeanVMTests.Guest.ModelRootWhir
