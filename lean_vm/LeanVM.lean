import LeanVM.Protocol.LeanVM
import LeanVM.Guest.EndFinal
import LeanVM.Guest.EndFinalComplete
import LeanVM.Guest.EndKnow
import LeanVM.Guest.Batch.Children
import LeanVM.Guest.Batch.Rom
import LeanVM.Protocol.EndToEnd.Blind.Statements
import LeanVM.Protocol.EndToEnd.Blind.Execution
import LeanVM.Protocol.EndToEnd.Blind.Deferred
import LeanVM.Guest.Value.OracleModel
import LeanVM.E2E.Runs
import LeanVM.E2E.Engine
import LeanVM.E2E.Da
import LeanVM.E2E.Batch
import LeanVM.Guest.EndKnowB
import LeanVM.E2E.Guest
import LeanVM.E2E.Complete.Tree
import LeanVM.E2E.Complete.TreeLog
import LeanVM.E2E.Complete.DecodeFinal
import LeanVM.E2E.Complete.Witness
import LeanVM.E2E.Complete.Count.FinalWitness
import LeanVM.E2E.Budget
import LeanVM.E2E.Termination
import LeanVM.E2E.Knowledge
import LeanVM.E2E.Sanity
import LeanVM.E2E.Bridge
import LeanVM.E2E.NoForgery
import LeanVM.E2E.Reduction.VerifyBound
import LeanVM.E2E.Deployed
import LeanVM.E2E.Vis.Deployed
import LeanVM.E2E.Complete.Rom.End

/-! The theorems: the verifier's, `LeanVM.KnowledgeSoundness` and `LeanVM.Completeness` (`LeanVM/Spec/Statement.lean`), and the deployed aggregation guest's: `AggregateSound` (what the outer verifier's acceptance establishes) and `GuestKnowledge` (`LeanVM/Spec/Guest.lean`), its witness read off the execution's memory by `LeanVM.Guest.End.decode`, with `decode_binds`; the recursion step `LeanVM.Guest.Batch.children_sound` and the batching in the random-oracle model `LeanVM.Guest.Batch.batch_rom`; `GuestSound` and `GuestCompleteWithin` (`LeanVM/Guest/End.lean`). The build fails if their axiom footprint ever grows beyond Lean's three standard axioms. -/

/-- info: 'LeanVM.knowledgeSoundness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.knowledgeSoundness_holds

/-- info: 'LeanVM.completeness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_holds

/-- info: 'LeanVM.Guest.End.guest_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_sound

/-- info: 'LeanVM.Guest.End.aggregate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound

/-- info: 'LeanVM.Guest.End.guest_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_complete

/-- info: 'LeanVM.Guest.End.aggregate_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_complete

/-- info: 'LeanVM.Guest.End.guest_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_knowledge

/-- info: 'LeanVM.Guest.End.aggregate_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_knowledge

/-- info: 'LeanVM.Guest.End.decode_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.decode_binds

/-- info: 'LeanVM.Guest.End.aggregate_sound_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound_outer

/-- info: 'LeanVM.Guest.Batch.children_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.children_sound

/-- info: 'LeanVM.Guest.Batch.batch_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rom

/-! The end-to-end security theorem's chain so far (`docs/roadmap/e2e-security.md`): T1 (the Flock-blind verifier's knowledge soundness, cache and probability forms; the deferred-verifier bridge), C5 (the oracle hash model), T5's run bridges, the game engine, E5 (the DA leg) and T7′ (V_I with BLAKE2s accepts what the deployed aggregation accepts, `idealVerify_blake2s`). -/

/-- info: 'LeanVM.Protocol.EndToEnd.Blind.blind_knowledge_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Protocol.EndToEnd.Blind.blind_knowledge_cache

/-- info: 'LeanVM.Protocol.EndToEnd.Blind.blindKnowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Protocol.EndToEnd.Blind.blindKnowledgeSoundness

/-- info: 'LeanVM.Protocol.EndToEnd.Blind.blindKnowledgeSoundness_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Protocol.EndToEnd.Blind.blindKnowledgeSoundness_execution

/-- info: 'LeanVM.Protocol.EndToEnd.Blind.execution_of_extractedBlind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Protocol.EndToEnd.Blind.execution_of_extractedBlind

/-- info: 'LeanVM.Protocol.Verifier.verifyBlindWith_of_verifyDeferredWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Protocol.Verifier.verifyBlindWith_of_verifyDeferredWith

/-- info: 'LeanVM.Protocol.Verifier.verifyBlindWith_of_verifyWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Protocol.Verifier.verifyBlindWith_of_verifyWith

/-- info: 'LeanVM.Guest.Value.stdChain_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Value.stdChain_snoc

/-- info: 'LeanVM.Guest.Value.validExecutionB_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Value.validExecutionB_oracle

/-- info: 'LeanVM.Guest.Value.tableOK_blake2s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Value.tableOK_blake2s

/-- info: 'LeanVM.E2E.run_simulateQ_randomOracle_of_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.run_simulateQ_randomOracle_of_answered

/-- info: 'LeanVM.E2E.xmssVerifyWith_eq_simulateQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.xmssVerifyWith_eq_simulateQ

/-- info: 'LeanVM.E2E.sphincsVerifyWith_eq_simulateQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincsVerifyWith_eq_simulateQ

/-- info: 'LeanVM.E2E.prEvent_game_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_game_le

/-- info: 'LeanVM.E2E.daBacked_of_not_daBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.daBacked_of_not_daBad

/-- info: 'LeanVM.E2E.prEvent_game_daBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_game_daBad_le

/-- info: 'LeanVM.E2E.bytecodeHolds_of_batchWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.bytecodeHolds_of_batchWith

/-- info: 'LeanVM.E2E.prEvent_game_batchBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_game_batchBad_le

/-- info: 'LeanVM.E2E.children_bytecodeHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.children_bytecodeHolds

/-- info: 'LeanVM.Guest.End.guest_knowledge_model_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.guest_knowledge_model_at

/-- info: 'LeanVM.Guest.End.guest_knowledge_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.guest_knowledge_model

/-- info: 'LeanVM.Guest.End.guest_knowledge_of_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.guest_knowledge_of_model

/-- info: 'LeanVM.E2E.rank_lt_of_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.rank_lt_of_child

/-- info: 'LeanVM.E2E.prEvent_game_pred_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_game_pred_le

/-- info: 'LeanVM.E2E.aggregate_knowledge_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_knowledge_cache

/-- info: 'LeanVM.E2E.aggregate_knowledge_cache'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_knowledge_cache'

/-- info: 'LeanVM.E2E.prEvent_game_aggregate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_game_aggregate_le

/-- info: 'LeanVM.E2E.guestHypsM_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.guestHypsM_model

/-- info: 'LeanVM.E2E.guest_knowledge_model_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.guest_knowledge_model_all

/-- info: 'LeanVM.E2E.aggregate_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_knowledge

/-- info: 'LeanVM.E2E.prEvent_game_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_game_aggregate

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete'

/-- info: 'LeanVM.E2E.Complete.honestOut_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestOut_isSome

/-! T6-det without a hypothesis on the guest (`docs/roadmap/t6-completeness.md`): the guest is complete over every completeness model (`guestCompleteModel`, L2), so V_I accepts the honest prover's idealized proof of any valid honest tree within the limits (L17 as a count on the node's log, decision T6-2 of `docs/roadmap/e2e-security.md`) on the good events G1–G3. -/

/-- info: 'LeanVM.E2E.Complete.guestCompleteModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.guestCompleteModel

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete''' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete''

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_det

/-! T6-det is not vacuous (`LeanVM/E2E/Complete/Witness.lean`): a leaf holding one leanXMSS claim
directly, at a constant `H`, meets all of `idealVerify_complete_det`'s hypotheses together
(`hyps_wTree`), so V_I accepts its honest idealized proof (`idealVerify_complete_wTree`). -/

/-- info: 'LeanVM.E2E.Complete.hyps_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.hyps_wTree

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_wTree

/-! L17 is a theorem (`docs/roadmap/l17-count.md`, decision T6-2 of `docs/roadmap/e2e-security.md`): under the deployed limits and the node relation, the node's log of hashed strings has fewer than `2^64` block prefixes (`nodeLog_count_lt`), so T6-det holds under the deployed limits and budget alone (`idealVerify_complete_final`), and the leaf meets its hypotheses (`idealVerify_complete_final_wTree`). -/

/-- info: 'LeanVM.E2E.Complete.nodeLog_count_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.nodeLog_count_lt

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_final

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_final_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_final_wTree

/-- info: 'LeanVM.E2E.run_idealVerify_budgetedQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.run_idealVerify_budgetedQuery

/-- info: 'LeanVM.E2E.game_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.game_accepted

/-- info: 'LeanVM.E2E.prEvent_game_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_game_accepted_le

/-- info: 'LeanVM.E2E.aggregate_knowledge_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_knowledge_sub

/-- info: 'LeanVM.E2E.XmssRed.prEvent_forgedX_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.XmssRed.prEvent_forgedX_le

/-- info: 'LeanVM.E2E.SphincsRed.prEvent_forgedS_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.SphincsRed.prEvent_forgedS_le

/-- info: 'LeanVM.E2E.prEvent_breaks_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_breaks_le

/-- info: 'LeanVM.E2E.aggregate_no_forgery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery

/-- info: 'LeanVM.E2E.verify_isTotalQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.verify_isTotalQueryBound

/-- info: 'LeanVM.E2E.Sanity.idealVerify_blake2s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Sanity.idealVerify_blake2s

/-! The end theorem of `docs/roadmap/e2e-security.md`, fully instantiated (`LeanVM/E2E/Deployed.lean`): T5 at leanXMSS's and leanSPHINCS's proved multi-user bounds and the proved costs of the honest signers and the final verifications, at each proved leanSPHINCS parameter set, with a closed-form error (`closedError`), and its value for one slot. -/

/-- info: 'LeanVM.E2E.aggregate_no_forgery_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_closed

/-- info: 'LeanVM.E2E.aggregate_no_forgery_deployed_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_deployed_full

/-- info: 'LeanVM.E2E.aggregate_no_forgery_deployed_pruned20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_deployed_pruned20

/-- info: 'LeanVM.E2E.aggregate_no_forgery_deployed_pruned14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_deployed_pruned14

/-- info: 'LeanVM.E2E.aggregate_no_forgery_deployed_pruned13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_deployed_pruned13

/-- info: 'LeanVM.E2E.aggregate_no_forgery_deployed_pruned12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_deployed_pruned12

/-- info: 'LeanVM.E2E.aggregate_no_forgery_deployed_pruned10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_deployed_pruned10

/-- info: 'LeanVM.E2E.aggregate_no_forgery_deployed_pruned8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_deployed_pruned8

/-- info: 'LeanVM.E2E.aggregate_no_forgery_deployed_full_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_deployed_full_sharp

/-- info: 'LeanVM.E2E.aggregate_no_forgery_deployed_pruned20_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_deployed_pruned20_sharp

/-- info: 'LeanVM.E2E.aggregate_no_forgery_one_slot_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_one_slot_full

/-- info: 'LeanVM.E2E.aggregate_no_forgery_one_slot_pruned20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_one_slot_pruned20

/-! The end theorem with the visible accounting (W-vis, `docs/roadmap/w-vis.md`, decisions E2E-6 and E2E-7): a break at V_I's trace, and today's `Breaks`, at most §0's bound in `Q_v = qH + budget` with the proved constants (`sec0ErrorGame`), equivalently §0's `ε(Q_v)` (`eps0Game`) plus the explicit deviations (`deltaGame`), from leanXMSS's and leanSPHINCS's proved single-key security, at each proved leanSPHINCS parameter set (`LeanVM/E2E/Vis/Deployed.lean`); one slot `≤ 2^-42 + 2^-51`, a lifetime `≤ 2^-41`. -/

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_eps0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_eps0

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_game

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_full

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_full_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_full_game

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_full_eps0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_full_eps0

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned20

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned20_eps0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned20_eps0

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_one_slot_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_one_slot_full

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_lifetime_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_lifetime_full

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_lifetime_full_eps0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_lifetime_full_eps0

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_lifetime_xmss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_lifetime_xmss

/-! T6-prob (`docs/roadmap/t6-prob.md`): V_I accepts the honest prover's idealized proof of a generated valid tree, over the random oracle, except with probability `completeError`; no good event is a hypothesis (G1, G2 bounded by `powPot` and `weightsPot`; G3 removed by decision E2E-8). Not vacuous: the honest leanXMSS leaf generator, error at most `2^-124`. -/

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_N

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_rom

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_rom_run

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_xmssLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_rom_xmssLeaf
