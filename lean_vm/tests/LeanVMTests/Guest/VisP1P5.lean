import LeanVM.E2E.Vis.Engine
import LeanVM.E2E.Vis.Knowledge

/-!
# Tests: W-vis P1 and P5, their axioms

The two-rate potential engine and the key-generation split (`LeanVM.E2E.Vis.Engine`, P1), and
T4 at V_I's trace with T3's conclusion `RankOK` as a hypothesis (`LeanVM.E2E.Vis.Knowledge`, P5),
rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.E2E.prEvent_run_le_twoRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_run_le_twoRate

/-- info: 'LeanVM.E2E.lintegral_run_le_of_budgetedPQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.lintegral_run_le_of_budgetedPQ

/-- info: 'LeanVM.E2E.gameRec_eq_keygen_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.gameRec_eq_keygen_bind

/-- info: 'LeanVM.E2E.restRec_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.restRec_keys

/-- info: 'LeanVM.E2E.prEvent_gameRec_le_of_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_gameRec_le_of_phase

/-- info: 'LeanVM.E2E.prEvent_gameRec_le_of_phase_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_gameRec_le_of_phase_const

/-- info: 'LeanVM.E2E.openingsWith_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.openingsWith_mono

/-- info: 'LeanVM.E2E.vectorDigestOfWith_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.vectorDigestOfWith_mono

/-- info: 'LeanVM.E2E.rows_codewords_of_not_daBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.rows_codewords_of_not_daBad

/-- info: 'LeanVM.E2E.daBacked_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.daBacked_trace

/-- info: 'LeanVM.E2E.heldDirectTrace_of_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.heldDirectTrace_of_node

/-- info: 'LeanVM.E2E.aggregate_knowledge_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_knowledge_trace

/-- info: 'LeanVM.E2E.aggregate_knowledge_trace_of_not_aggBadT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_knowledge_trace_of_not_aggBadT

/-- info: 'LeanVM.E2E.gameRec_knows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.gameRec_knows
