import LeanVM.Guest.B1.Comp.Sig.SphincsKey
import LeanVM.Guest.B1.Comp.Sig.SphincsFold
import LeanVM.Guest.B1.Comp.Sig.SphincsCoord

/-!
# Tests: leanSPHINCS's forest keys, folds and coordinates over a completeness model, their axioms

`sp_forest_key__L{t}`, the forest folds and a coordinate's blocks over a `CompModel`
(`LeanVM.Guest.B1.Comp.Sig.SphincsKey`, `SphincsFold`, `SphincsCoord`), and the deployed lemmas
recovered from them at `CompModel.deployed`, rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.Sig.fChainWith_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.fChainWith_eq_some_iff

/-- info: 'LeanVM.Guest.B1.Sig.fkLeafWith_iff_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.fkLeafWith_iff_C

/-- info: 'LeanVM.Guest.B1.Sig.fkStep_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.fkStep_comp

/-- info: 'LeanVM.Guest.B1.Sig.fkChain_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.fkChain_comp

/-- info: 'LeanVM.Guest.B1.Sig.fkChains_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.fkChains_comp

/-- info: 'LeanVM.Guest.B1.Sig.fkTail_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.fkTail_comp

/-- info: 'LeanVM.Guest.B1.Sig.fkBody_holdsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.fkBody_holdsB

/-- info: 'LeanVM.Guest.B1.Sig.sp_forest_key_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sp_forest_key_comp

/-- info: 'LeanVM.Guest.B1.Sig.sp_forest_key_rel_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sp_forest_key_rel_comp

/-- info: 'LeanVM.Guest.B1.Sig.sp_forest_key_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sp_forest_key_of_comp

/-- info: 'LeanVM.Guest.B1.Sig.fkCompleteC_relB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.fkCompleteC_relB

/-- info: 'LeanVM.Guest.B1.Sig.spLevel_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.spLevel_comp

/-- info: 'LeanVM.Guest.B1.Sig.spLevels_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.spLevels_comp

/-- info: 'LeanVM.Guest.B1.Sig.spArm_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.spArm_comp

/-- info: 'LeanVM.Guest.B1.Sig.spMatch_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.spMatch_comp

/-- info: 'LeanVM.Guest.B1.Sig.spMatch_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.spMatch_of_comp

/-- info: 'LeanVM.Guest.B1.Sig.sSubPre_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sSubPre_comp

/-- info: 'LeanVM.Guest.B1.Sig.sSub_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sSub_comp

/-- info: 'LeanVM.Guest.B1.Sig.coordD_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.coordD_comp

/-- info: 'LeanVM.Guest.B1.Sig.subTree_someC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.subTree_someC

/-- info: 'LeanVM.Guest.B1.Sig.sCoordT_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sCoordT_comp

/-- info: 'LeanVM.Guest.B1.Sig.sCoord_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sCoord_comp

/-- info: 'LeanVM.Guest.B1.Sig.sCoords_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sCoords_comp
