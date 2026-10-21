import LeanVM.Guest.B1.Comp.Whir.Loc.OsAllC

/-!
# Tests: `open_stacked` placed over every completeness model, its axioms

The located completeness of `open_stacked` over a `CompModel` (`LeanVM.Guest.B1.Comp.Whir.Loc.*`:
the run's data and buffers over a total hash, the callees composed under `CM.sem`, the 50
specializations of `opening_queries`, the 28 configurations, group 1's callees over the model, the
pure callees' sizes), the cap's meaning over the model (`OsCapC`), the caps' agreement over a total
hash (`CapAgreesW`), and the deployed lemma recovered at `CompModel.deployed`, rest on Lean's three
standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.open_stacked_completeAtBC_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.open_stacked_completeAtBC_b2c

/-- info: 'LeanVM.Guest.B1.open_stacked_completeAtBC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.open_stacked_completeAtBC_of

/-- info: 'LeanVM.Guest.B1.open_stacked_completeAtB_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.open_stacked_completeAtB_of_comp

/-- info: 'LeanVM.Guest.B1.osBopC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osBopC_eq

/-- info: 'LeanVM.Guest.B1.open_stacked_completeAtBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.open_stacked_completeAtBC

/-- info: 'LeanVM.Guest.B1.os_completeOpenAtBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_completeOpenAtBC

/-- info: 'LeanVM.Guest.B1.OsData.kids_atBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.OsData.kids_atBC

/-- info: 'LeanVM.Guest.B1.OsData.body_atC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.OsData.body_atC

/-- info: 'LeanVM.Guest.B1.os_kit_of_runC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_kit_of_runC

/-- info: 'LeanVM.Guest.B1.opening_queries_completeAtC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_queries_completeAtC

/-- info: 'LeanVM.Guest.B1.oqLoop_completeAtC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqLoop_completeAtC

/-- info: 'LeanVM.Guest.B1.oqLoop_relAtInC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqLoop_relAtInC

/-- info: 'LeanVM.Guest.B1.oqLoop_iterC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqLoop_iterC

/-- info: 'LeanVM.Guest.B1.oqAns_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqAns_deployed

/-- info: 'LeanVM.Guest.B1.sqLoop_relAtInC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sqLoop_relAtInC

/-- info: 'LeanVM.Guest.B1.grind_check_completeRelBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.grind_check_completeRelBC

/-- info: 'LeanVM.Guest.B1.opening_ood_point_completeRelBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_ood_point_completeRelBC

/-- info: 'LeanVM.Guest.B1.opening_fold_completeRelBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_fold_completeRelBC

/-- info: 'LeanVM.Guest.B1.ofm_L4_completeMemBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.ofm_L4_completeMemBC

/-- info: 'LeanVM.Guest.B1.osDecodeAtDC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osDecodeAtDC_of

/-- info: 'LeanVM.Guest.B1.osPureSizes_capC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osPureSizes_capC

/-- info: 'LeanVM.Guest.B1.osCap_meaningC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osCap_meaningC

/-- info: 'LeanVM.Guest.B1.os_cap_hashedC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_cap_hashedC

/-- info: 'LeanVM.Guest.B1.OsData.lv_ansC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.OsData.lv_ansC

/-- info: 'LeanVM.Guest.B1.oqAns_of_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqAns_of_opening

/-- info: 'LeanVM.Guest.B1.osCapAns_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osCapAns_of

/-- info: 'LeanVM.Guest.B1.capAgreesW_iff_with' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.capAgreesW_iff_with

/-- info: 'LeanVM.Guest.B1.capAgreesW_blake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.capAgreesW_blake

/-- info: 'LeanVM.Guest.B1.queriesOfW_eq_queriesOfWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.queriesOfW_eq_queriesOfWith

/-- info: 'LeanVM.Guest.B1.oq_completeAtB_L0_L16_L6_L14_L5C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oq_completeAtB_L0_L16_L6_L14_L5C

/-- info: 'LeanVM.Guest.B1.oq_completeAtB_L1_L64_L8_L26_L6C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oq_completeAtB_L1_L64_L8_L26_L6C

/-- info: 'LeanVM.Guest.B1.osKidsAtB_0C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osKidsAtB_0C

/-- info: 'LeanVM.Guest.B1.osKidsAtB_27C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osKidsAtB_27C

/-- info: 'LeanVM.Guest.B1.os_tail_dataC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_tail_dataC

/-- info: 'LeanVM.Guest.B1.OsData.lvsCallHBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.OsData.lvsCallHBC
