import LeanVM.Guest.B1.Comp.Whir.QueriesIter
import LeanVM.Guest.B1.Comp.Whir.StackedDeployed
import LeanVM.Guest.B1.Comp.Whir.OpenAns

/-!
# Tests: Whir's opening queries and stacked opening over a completeness model, their axioms

The completeness over a `CompModel` of `opening_queries`' loop (`LeanVM.Guest.B1.Comp.Whir.Queries*`)
and of `open_stacked`'s body, its blocks and its squeeze loop (`LeanVM.Guest.B1.Comp.Whir.Stacked*`,
`OsBody`, `OsDataC`, `SqIter`), the run's inversions with what the model answers, and the deployed
lemmas recovered from them at `CompModel.deployed` (`…_of_comp`), rest on Lean's three standard
axioms only.
-/

/-- info: 'LeanVM.Guest.B1.climb_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.climb_answered

/-- info: 'LeanVM.Guest.B1.oqLeaf_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqLeaf_completeC

/-- info: 'LeanVM.Guest.B1.oqPathT_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqPathT_completeC

/-- info: 'LeanVM.Guest.B1.oqLeaf_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqLeaf_complete_of_comp

/-- info: 'LeanVM.Guest.B1.oqPathT_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqPathT_complete_of_comp

/-- info: 'LeanVM.Guest.B1.oqIter_holdsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqIter_holdsC

/-- info: 'LeanVM.Guest.B1.oqIterValC_ptrs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqIterValC_ptrs

/-- info: 'LeanVM.Guest.B1.oqIterValC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqIterValC_deployed

/-- info: 'LeanVM.Guest.B1.oqIter_holds_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqIter_holds_of_comp

/-- info: 'LeanVM.Guest.B1.runsM_runsW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.runsM_runsW

/-- info: 'LeanVM.Guest.B1.ansRun_blake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.ansRun_blake

/-- info: 'LeanVM.Guest.B1.AnsRun.bind_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.AnsRun.bind_inv

/-- info: 'LeanVM.Guest.B1.AnsRun.bind_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.AnsRun.bind_of

/-- info: 'LeanVM.Guest.B1.ansRun_foldStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.ansRun_foldStep

/-- info: 'LeanVM.Guest.B1.ansRun_sampleQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.ansRun_sampleQueries

/-- info: 'LeanVM.Guest.B1.os_lq_ansC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_lq_ansC

/-- info: 'LeanVM.Guest.B1.os_level_invC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_level_invC

/-- info: 'LeanVM.Guest.B1.os_chain_of_runC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_chain_of_runC

/-- info: 'LeanVM.Guest.B1.os_open_invC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_open_invC

/-- info: 'LeanVM.Guest.B1.os_chain_tailC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_chain_tailC

/-- info: 'LeanVM.Guest.B1.os_tail_invC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_tail_invC

/-- info: 'LeanVM.Guest.B1.os_tailOpen_invC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_tailOpen_invC

/-- info: 'LeanVM.Guest.B1.osFsNext_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osFsNext_completeC

/-- info: 'LeanVM.Guest.B1.osFolds_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osFolds_completeC

/-- info: 'LeanVM.Guest.B1.osFinal_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osFinal_completeC

/-- info: 'LeanVM.Guest.B1.osOodSample_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osOodSample_completeC

/-- info: 'LeanVM.Guest.B1.osCommit_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osCommit_completeC

/-- info: 'LeanVM.Guest.B1.osGrind_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osGrind_completeC

/-- info: 'LeanVM.Guest.B1.osSqueezes_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osSqueezes_completeC

/-- info: 'LeanVM.Guest.B1.osQueries_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osQueries_completeC

/-- info: 'LeanVM.Guest.B1.osTail_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osTail_completeC

/-- info: 'LeanVM.Guest.B1.osHead_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osHead_completeC

/-- info: 'LeanVM.Guest.B1.osLevelA_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osLevelA_completeC

/-- info: 'LeanVM.Guest.B1.osLevelB_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osLevelB_completeC

/-- info: 'LeanVM.Guest.B1.osLevel_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osLevel_completeC

/-- info: 'LeanVM.Guest.B1.osLevels_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osLevels_completeC

/-- info: 'LeanVM.Guest.B1.osBody_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osBody_completeC

/-- info: 'LeanVM.Guest.B1.sqIter_holdsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sqIter_holdsC

/-- info: 'LeanVM.Guest.B1.osLvAns_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osLvAns_deployed

/-- info: 'LeanVM.Guest.B1.osChainC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osChainC_deployed

/-- info: 'LeanVM.Guest.B1.osFsNext_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osFsNext_complete_of_comp

/-- info: 'LeanVM.Guest.B1.osFolds_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osFolds_complete_of_comp

/-- info: 'LeanVM.Guest.B1.osCommit_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osCommit_complete_of_comp

/-- info: 'LeanVM.Guest.B1.osGrind_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osGrind_complete_of_comp

/-- info: 'LeanVM.Guest.B1.osSqueezes_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osSqueezes_complete_of_comp

/-- info: 'LeanVM.Guest.B1.osQueries_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osQueries_complete_of_comp

/-- info: 'LeanVM.Guest.B1.osTail_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osTail_complete_of_comp

/-- info: 'LeanVM.Guest.B1.osHead_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osHead_complete_of_comp

/-- info: 'LeanVM.Guest.B1.sqIter_holds_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sqIter_holds_of_comp

/-- info: 'LeanVM.Guest.B1.osBody_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osBody_complete_of_comp

/-- info: 'LeanVM.Guest.B1.os_open_inv_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_open_inv_of_comp

/-- info: 'LeanVM.Guest.B1.os_tailOpen_inv_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_tailOpen_inv_of_comp

/-- info: 'LeanVM.Guest.B1.openOne_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.openOne_answered

/-- info: 'LeanVM.Guest.B1.openAll_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.openAll_answered

/-- info: 'LeanVM.Guest.B1.sqAllM_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sqAllM_steps
