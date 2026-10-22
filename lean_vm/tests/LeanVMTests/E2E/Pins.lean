import LeanVM.E2E.SanityDeployedBudget
import LeanVM.E2E.Complete.Rom.RootGen
import LeanVM.E2E.Complete.Rom.PadRec
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
import LeanVM.E2E.Headline
import LeanVM.E2E.HeadlineSharp
import LeanVM.E2E.SanityDeployed.Witness

/-!
# Tests: the axiom footprint of the end-to-end chain's intermediate theorems

`LeanVM.lean` pins the end theorems only (the verifier's and the guest's, and
`LeanVM/E2E/Main.lean`'s). The end-to-end chain's intermediate theorems, and the end theorems the
headline supersedes (the closed-form and visible-accounting families, the T6 variants, S1's forms),
are pinned here (decision E2E-12): every one of them rests on Lean's three axioms.
-/

/-! The end-to-end security theorem's chain so far (`docs/roadmap/e2e-security.md`): T1 (the Flock-blind verifier's knowledge soundness, cache and probability forms; the deferred-verifier bridge), C5 (the oracle hash model), T5's run bridges, the game engine, E5 (the DA leg) and T7′ (V_I with BLAKE2s accepts what the deployed aggregation accepts, `idealVerify_blake2s` with full words, `idealVerify_blake2s_known` with partial words whose present columns encode a known stack, decision E2E-10). -/

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

/-- info: 'LeanVM.E2E.Sanity.idealVerify_blake2s_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Sanity.idealVerify_blake2s_known

/-! **The headline** (`LeanVM/E2E/Headline.lean`, `docs/roadmap/headline.md`): for every leanSPHINCS parameter set (`SphincsSet`), every numbers of keys and every adversary, V_I on at most `N` nodes with the budget `viCost N` accepts a forged claim or an unbacked DA claim with probability at most `q · 2^-λ₁ + 30 q²/2^256`, `q` every hash evaluation of the game; `λ₁ = 106` at `2^20 + 2^20` keys, `126` with leanXMSS keys only. -/

/-- info: 'LeanVM.E2E.aggregate_no_forgery_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_final

/-- info: 'LeanVM.E2E.aggregate_no_forgery_final_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_final_deployed

/-- info: 'LeanVM.E2E.aggregate_no_forgery_final_xmss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_final_xmss

/-! **The headline's budget covers honest proofs** (`LeanVM/E2E/Headline.lean`): `viNodeCost = 179,733,089 ≈ 2^27.42` is the proved bound on V_I's queries per honest node and at the root (`viNodeCost_eq`), so V_I on `N` nodes makes at most `viCost N` queries on the honest proof of a tree of at most `N` nodes (`queryCount_honest_le_viCost`), and the game's V_I, budget `viCost N` and all, accepts the honest proof of a generated valid tree except with T6-prob's `completeError` (`aggregate_complete_final`). -/

/-- info: 'LeanVM.E2E.queryCount_honest_le_viCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.queryCount_honest_le_viCost

/-- info: 'LeanVM.E2E.aggregate_complete_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_complete_final

/-! **The sharp headline** (`LeanVM/E2E/HeadlineSharp.lean`): the headline with leanSPHINCS's per-key multi-user bound (`SphincsSetSharp`, every proved set, the certificates' constants evaluated by the kernel): `q · 2^-λ₁ + (30 + D n_s) q²/2^256`, `λ₁ = 116` at `2^20 + 2^20` keys for `full` and `pruned20`, with `30 + D 2^20 ≤ 2^34`. -/

/-- info: 'LeanVM.E2E.aggregate_no_forgery_final_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_final_sharp

/-- info: 'LeanVM.E2E.aggregate_no_forgery_final_sharp_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_final_sharp_deployed

/-- info: 'LeanVM.E2E.sharp_full_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sharp_full_deployed

/-- info: 'LeanVM.E2E.sharp_pruned20_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sharp_pruned20_deployed

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

/-! T6-prob (`docs/roadmap/t6-prob.md`): V_I accepts the honest prover's idealized proof of a generated valid tree, over the random oracle, except with probability `completeError`; no good event is a hypothesis (G1, G2 bounded by `powPot` and `weightsPot`; G3 removed by decision E2E-8). Not vacuous: the honest leanXMSS leaf generator, and a root over it (recursion: the batching, the child's decoding, the stack-log floor), error at most `2^-124`; at any depth, the honest prover padding each node's memory as leanVM's does (`guestCompleteModel_big`, `idealVerify_complete_rom_rec`). -/

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

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_xmssRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_rom_xmssRoot

/-- info: 'LeanVM.E2E.Complete.guestCompleteModel_big' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.guestCompleteModel_big

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_rom_rec

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_rec_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_rom_rec_budget

/-! V_I's queries on the honest proof (`LeanVM/E2E/Complete/Rom/ViCost.lean`): at most `viRootBound + fuel · viStepBound`, `13,508 + fuel · 179,719,581`, for every hash; and T6-prob with the game's budget (`LeanVM/E2E/Complete/Rom/EndBudget.lean`): V_I run as the game runs it, with the budgeted hash and a budget of at least `N · viNodeBound`, after the honest prover against the same lazily sampled oracle, rejects with probability at most `completeError`. -/

/-- info: 'LeanVM.E2E.Complete.queryCount_honest_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.queryCount_honest_le

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_rom_budget

/-! The deployed system's honest aggregation at BLAKE2s (`LeanVM/E2E/SanityDeployed.lean`): the deployed verifier accepts it, and V_I accepts its idealized proof, unless an explicit BLAKE2s compression collision exists; the deployed-faithful prover outputs on every valid tree within the limits whose proof-of-work searches succeed, and on an honest leanXMSS leaf. -/

/-- info: 'LeanVM.E2E.SanityDeployed.sanity_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.SanityDeployed.sanity_deployed

/-- info: 'LeanVM.E2E.SanityDeployed.sanity_deployed_of_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.SanityDeployed.sanity_deployed_of_tree

/-- info: 'LeanVM.E2E.SanityDeployed.sanity_deployed_xmssLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.SanityDeployed.sanity_deployed_xmssLeaf

/-- info: 'LeanVM.E2E.SanityDeployed.queryCount_deployed_le_viCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.SanityDeployed.queryCount_deployed_le_viCost

/-- info: 'LeanVM.E2E.SanityDeployed.sanity_deployed_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.SanityDeployed.sanity_deployed_budget

/-- info: 'LeanVM.E2E.SanityDeployed.sanity_deployed_budget_of_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.SanityDeployed.sanity_deployed_budget_of_tree
