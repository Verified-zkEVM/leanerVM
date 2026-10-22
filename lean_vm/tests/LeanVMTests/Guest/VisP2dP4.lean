import LeanVM.E2E.Vis.Count
import LeanVM.E2E.Vis.Pred

/-!
# Tests: W-vis P2d and P4, their axioms

The counts of the visible accounting (`LeanVM.E2E.Vis.Count`, P2d: key generation logs only hidden
inputs, the rest of the game makes at most `qH + budget` visible queries) and T3 restricted to
non-hidden entries (`LeanVM.E2E.Vis.Pred`, P4: `PredS`, its potential, `RankOK` from it) rest on
Lean's three standard axioms only.
-/

/-- info: 'LeanVM.E2E.logsSat_hashRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.logsSat_hashRun

/-- info: 'LeanVM.E2E.logsSat_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.logsSat_keygen

/-- info: 'LeanVM.E2E.keygenRun_hid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.keygenRun_hid

/-- info: 'LeanVM.E2E.keygenPhase_hid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.keygenPhase_hid

/-- info: 'LeanVM.E2E.costsP_simulateQ_advImpl_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.costsP_simulateQ_advImpl_vis

/-- info: 'LeanVM.E2E.costsP_restBody_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.costsP_restBody_vis

/-- info: 'LeanVM.E2E.costs_restBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.costs_restBody

/-- info: 'LeanVM.E2E.isQueryBoundP_restRec_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.isQueryBoundP_restRec_vis

/-- info: 'LeanVM.E2E.isQueryBoundP_restRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.isQueryBoundP_restRec

/-- info: 'LeanVM.E2E.predS_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.predS_append

/-- info: 'LeanVM.E2E.predPotS_step_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.predPotS_step_vis

/-- info: 'LeanVM.E2E.predPotS_step_hid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.predPotS_step_hid

/-- info: 'LeanVM.E2E.predPotS_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.predPotS_mono

/-- info: 'LeanVM.E2E.predPotS_of_allHid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.predPotS_of_allHid

/-- info: 'LeanVM.E2E.not_inPfx_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.not_inPfx_seed

/-- info: 'LeanVM.E2E.not_hid_stmtInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.not_hid_stmtInput

/-- info: 'LeanVM.E2E.rank_lt_of_child_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.rank_lt_of_child_vis

/-- info: 'LeanVM.E2E.rankOK_of_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.rankOK_of_pred

/-- info: 'LeanVM.E2E.rankOK_of_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.rankOK_of_vis
