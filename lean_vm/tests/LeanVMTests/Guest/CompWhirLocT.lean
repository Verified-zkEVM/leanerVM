import LeanVM.Guest.B1.Comp.Whir.LocT.OsAllT

/-!
# Tests: `open_stacked` in tree form over every completeness model, its axioms

The tree form of `open_stacked`'s completeness over a `CompModel` (`LeanVM.Guest.B1.Comp.Whir.LocT.*`:
the callees composed with predicates, `opening_queries` and its loop by trees decoding to the
queries' openings at the 50 specializations, the cap's siblings from `verify_merkle_cap`'s load
equations, the root's decoding level by level, the 28 configurations, the run's stream length),
`CompleteOpenAtBCL … (CapAgreesC CM) … OsQ` at `main`'s frame sizes, rests on Lean's three standard
axioms only.
-/

/-- info: 'LeanVM.Guest.B1.open_stacked_completeAtBCL_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.open_stacked_completeAtBCL_b2c

/-- info: 'LeanVM.Guest.B1.open_stacked_completeAtBCL_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.open_stacked_completeAtBCL_of

/-- info: 'LeanVM.Guest.B1.open_stacked_completeAtBCL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.open_stacked_completeAtBCL

/-- info: 'LeanVM.Guest.B1.os_caseT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_caseT

/-- info: 'LeanVM.Guest.B1.os_completeOpenAtBCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_completeOpenAtBCT

/-- info: 'LeanVM.Guest.B1.OsData.os_decQC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.OsData.os_decQC

/-- info: 'LeanVM.Guest.B1.OsData.lvDecC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.OsData.lvDecC

/-- info: 'LeanVM.Guest.B1.OsData.kids_atBCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.OsData.kids_atBCT

/-- info: 'LeanVM.Guest.B1.os_completeAt_placeBCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_completeAt_placeBCT

/-- info: 'LeanVM.Guest.B1.OsData.lvsCallHBCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.OsData.lvsCallHBCT

/-- info: 'LeanVM.Guest.B1.OsData.lvCallQBCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.OsData.lvCallQBCT

/-- info: 'LeanVM.Guest.B1.OsData.lvCallCapBCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.OsData.lvCallCapBCT

/-- info: 'LeanVM.Guest.B1.os_levels_kidsBCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_levels_kidsBCT

/-- info: 'LeanVM.Guest.B1.opening_queries_completeAtCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_queries_completeAtCT

/-- info: 'LeanVM.Guest.B1.oqLoop_completeAtCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqLoop_completeAtCT

/-- info: 'LeanVM.Guest.B1.oqLoop_relAtInCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqLoop_relAtInCT

/-- info: 'LeanVM.Guest.B1.oqLoop_iterCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqLoop_iterCT

/-- info: 'LeanVM.Guest.B1.oqOpeningOf_iterC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oqOpeningOf_iterC

/-- info: 'LeanVM.Guest.B1.relAtInBT_of_walk_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.relAtInBT_of_walk_loop

/-- info: 'LeanVM.Guest.B1.capSibs_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.capSibs_agree

/-- info: 'LeanVM.Guest.B1.capSibs_honestW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.capSibs_honestW

/-- info: 'LeanVM.Guest.B1.os_kit_of_runCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_kit_of_runCT

/-- info: 'LeanVM.Guest.B1.validB_loadEqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.validB_loadEqns

/-- info: 'LeanVM.Guest.B1.nodeAgree_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.nodeAgree_read

/-- info: 'LeanVM.Guest.B1.osp_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osp_flatten

/-- info: 'LeanVM.Guest.B1.osLevelsOs_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osLevelsOs_range

/-- info: 'LeanVM.Guest.B1.kidsSat_zip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.kidsSat_zip

/-- info: 'LeanVM.Guest.B1.oq_completeAtBT_L1_L64_L8_L17_L8C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oq_completeAtBT_L1_L64_L8_L17_L8C

/-- info: 'LeanVM.Guest.B1.oq_completeAtBT_L0_L16_L6_L14_L5C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.oq_completeAtBT_L0_L16_L6_L14_L5C

/-- info: 'LeanVM.Guest.B1.osKidsAtBT_0C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osKidsAtBT_0C

/-- info: 'LeanVM.Guest.B1.osKidsAtBT_27C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osKidsAtBT_27C

/-- info: 'LeanVM.Guest.B1.osRootCells_0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osRootCells_0

/-- info: 'LeanVM.Guest.B1.osRootCells_27' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osRootCells_27

/-- info: 'LeanVM.Guest.B1.osCapNames_0' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osCapNames_0

/-- info: 'LeanVM.Guest.B1.osCapNames_27' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osCapNames_27

/-- info: 'LeanVM.Guest.B1.osCfgOf_0' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osCfgOf_0

/-- info: 'LeanVM.Guest.B1.vmcName_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.vmcName_eq

/-- info: 'LeanVM.Guest.B1.vmcCapLoads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.vmcCapLoads
