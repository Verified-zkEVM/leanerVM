import LeanVM.E2E.Vis.PerKey.XmssChain

/-!
# Tests: W-vis P7b (leanXMSS), the per-key bound

The per-key leanXMSS bound `prEvent_xWinAt_le` and its steps: key generation caches nothing private
for its own key, the challenger's log is key `j`'s record, the final check passes on a win, and the
single-key game is key generation followed by the reduction's run. They rest on Lean's three
standard axioms only.
-/

open LeanVM.E2E LeanVM.E2E.PerKeyX

-- outside the private class, a trace's answers are kept; inside, dropped
example (tr : LeanVM.Protocol.Compile.Rom.Log) (x : List UInt8) (h : PrivJ [] x) :
    lookOff (PrivJ []) tr x = none := by simp [lookOff, h]

example (tr : LeanVM.Protocol.Compile.Rom.Log) (x : List UInt8) (h : ¬ PrivJ [] x) :
    lookOff (PrivJ []) tr x = LeanVM.Protocol.Compile.Rom.look tr x := by simp [lookOff, h]

/-- info: 'LeanVM.E2E.cache_of_allQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.cache_of_allQueries

/-- info: 'LeanVM.E2E.PerKeyX.keygen_cache_not_privJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.keygen_cache_not_privJ

/-- info: 'LeanVM.E2E.PerKeyX.goodKeys_of_not_keyCollAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.goodKeys_of_not_keyCollAt

/-- info: 'LeanVM.E2E.PerKeyX.xBodyJ_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.xBodyJ_log

/-- info: 'LeanVM.E2E.cacheHas_lookOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.cacheHas_lookOff

/-- info: 'LeanVM.E2E.PerKeyX.run_finishJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.run_finishJ

/-- info: 'LeanVM.E2E.PerKeyX.simulateQ_σJ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.simulateQ_σJ_eq

/-- info: 'LeanVM.E2E.PerKeyX.forgeAdvantage_eq'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.forgeAdvantage_eq'

/-- info: 'LeanVM.E2E.PerKeyX.route_RJ_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.route_RJ_self

/-- info: 'LeanVM.E2E.PerKeyX.gameCore_xRedJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.gameCore_xRedJ

/-- info: 'LeanVM.E2E.PerKeyX.prEvent_RJ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.prEvent_RJ_le

/-- info: 'LeanVM.E2E.PerKeyX.prEvent_xWinAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.prEvent_xWinAt_le

/-- info: 'LeanVM.E2E.romRun_sequenceFin_front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.romRun_sequenceFin_front
