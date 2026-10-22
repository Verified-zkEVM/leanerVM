import LeanVM.E2E.Vis.PerKey.SphincsChain

/-!
# Tests: W-vis P7b (leanSPHINCS, the per-key bound), its axioms

The per-key leanSPHINCS chain (`LeanVM.E2E.Vis.PerKey.SphincsFacts`, `SphincsLog`, `SphincsFinal`,
`SphincsChain`) and its bound `prEvent_sWinAt_le` rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.E2E.PerKeyS.keygen_cache_not_privJS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.keygen_cache_not_privJS

/-- info: 'LeanVM.E2E.PerKeyS.goodKeysS_of_not_keyCollAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.goodKeysS_of_not_keyCollAt

/-- info: 'LeanVM.E2E.PerKeyS.sBodyJ_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.sBodyJ_log

/-- info: 'LeanVM.E2E.sphincsVerifyWith_lookOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincsVerifyWith_lookOff

/-- info: 'LeanVM.E2E.PerKeyS.run_finishJS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.run_finishJS

/-- info: 'LeanVM.E2E.PerKeyS.forgeAdvantage_eqS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.forgeAdvantage_eqS

/-- info: 'LeanVM.E2E.PerKeyS.gameCore_sRedJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.gameCore_sRedJ

/-- info: 'LeanVM.E2E.PerKeyS.prEvent_RJS_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.prEvent_RJS_le

/-- info: 'LeanVM.E2E.PerKeyS.romRun_sts_front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.romRun_sts_front

/-- info: 'LeanVM.E2E.PerKeyS.prEvent_sWinAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.prEvent_sWinAt_le
