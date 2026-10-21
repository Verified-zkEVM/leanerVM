import LeanVM.Guest.B1.Comp.CompletesB
import LeanVM.Guest.B1.Comp.Sig.Xmss
import LeanVM.Guest.B1.Comp.Sig.Sphincs

/-!
# Tests: the signature verifiers over a completeness model, their axioms

The `CompletesB` framework (`LeanVM.Guest.B1.Comp.CompletesB`), the honest values over a
`CompModel` (`Comp/Sig/Values.lean`), the completeness of `verify_lean_xmss` and
`verify_sig_lean_sphincs` and of their templates over a `CompModel` (`LeanVM.Guest.B1.Comp.Sig`),
the scheme runs taken apart, and the deployed completeness lemmas recovered from them at
`CompModel.deployed`, rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.of_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.of_deployed

/-- info: 'LeanVM.Guest.B1.Sig.completesB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.completesB_deployed

/-- info: 'LeanVM.Guest.B1.Sig.holdsListB_iff_of_freeIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.holdsListB_iff_of_freeIn

/-- info: 'LeanVM.Guest.B1.Sig.completesB_iff_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.completesB_iff_free

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.of_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.of_free

/-- info: 'LeanVM.Guest.B1.Sig.holdsListB_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.holdsListB_frame

/-- info: 'LeanVM.Guest.B1.Sig.atomB_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.atomB_frame

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.append

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.mono

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.nil

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.of_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.of_ext

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.withExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.withExt

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.withHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.withHolds

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.post

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.append_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.append_holds

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.append_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.append_tail

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.append_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.append_atom

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.atom_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.atom_cons

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.atom_cons0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.atom_cons0

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.hint_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.hint_cons

/-- info: 'LeanVM.Guest.B1.Sig.completesB_upds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.completesB_upds

/-- info: 'LeanVM.Guest.B1.Sig.completesB_setv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.completesB_setv

/-- info: 'LeanVM.Guest.B1.Sig.completesB_hint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.completesB_hint

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.flatten

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.flatMap_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.flatMap_range

/-- info: 'LeanVM.Guest.B1.Sig.relB_of_completesB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.relB_of_completesB

/-- info: 'LeanVM.Guest.B1.Sig.hbWith_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.hbWith_eq_some_iff

/-- info: 'LeanVM.Guest.B1.Sig.hcellWith_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.hcellWith_eq_some_iff

/-- info: 'LeanVM.Guest.B1.Sig.compress4_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress4_C

/-- info: 'LeanVM.Guest.B1.Sig.compress3_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress3_C

/-- info: 'LeanVM.Guest.B1.Sig.compress_two_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress_two_C

/-- info: 'LeanVM.Guest.B1.Sig.chainFromWith_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.chainFromWith_eq_some_iff

/-- info: 'LeanVM.Guest.B1.Sig.tipPairWith_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.tipPairWith_eq_some_iff

/-- info: 'LeanVM.Guest.B1.Sig.chainFromC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.chainFromC_deployed

/-- info: 'LeanVM.Guest.B1.Sig.tipPairC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.tipPairC_deployed

/-- info: 'LeanVM.Guest.B1.Sig.tipSetC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.tipSetC_deployed

/-- info: 'LeanVM.Guest.B1.Sig.tipSetWith_of_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.tipSetWith_of_C

/-- info: 'LeanVM.Guest.B1.Sig.mFoldWith_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.mFoldWith_eq_some_iff

/-- info: 'LeanVM.Guest.B1.Sig.mFoldC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.mFoldC_deployed

/-- info: 'LeanVM.Guest.B1.Sig.cStep_holdsB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.cStep_holdsB_of

/-- info: 'LeanVM.Guest.B1.Sig.cStep_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.cStep_comp

/-- info: 'LeanVM.Guest.B1.Sig.cSteps_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.cSteps_comp

/-- info: 'LeanVM.Guest.B1.Sig.cWalk_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.cWalk_comp

/-- info: 'LeanVM.Guest.B1.Sig.cWalks_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.cWalks_comp

/-- info: 'LeanVM.Guest.B1.Sig.armTail_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.armTail_comp

/-- info: 'LeanVM.Guest.B1.Sig.cArm_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.cArm_comp

/-- info: 'LeanVM.Guest.B1.Sig.cGroup_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.cGroup_comp

/-- info: 'LeanVM.Guest.B1.Sig.cGroups_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.cGroups_comp

/-- info: 'LeanVM.Guest.B1.Sig.cCodeword_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.cCodeword_comp

/-- info: 'LeanVM.Guest.B1.Sig.hvBlock_compS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.hvBlock_compS

/-- info: 'LeanVM.Guest.B1.Sig.hashValues_compS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.hashValues_compS

/-- info: 'LeanVM.Guest.B1.Sig.hashValues_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.hashValues_comp

/-- info: 'LeanVM.Guest.B1.Sig.hashValues_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.hashValues_of_comp

/-- info: 'LeanVM.Guest.B1.Sig.merkleLevel_holdsB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.merkleLevel_holdsB_of

/-- info: 'LeanVM.Guest.B1.Sig.merkle_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.merkle_comp

/-- info: 'LeanVM.Guest.B1.Sig.merkle_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.merkle_of_comp

/-- info: 'LeanVM.Guest.B1.Sig.tweakableHash_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.tweakableHash_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.chainWalk_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.chainWalk_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.recoverChain_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.recoverChain_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.leafHash_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.leafHash_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.messageDigest_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.messageDigest_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.treeFold_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.treeFold_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.layerRoot_someW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.layerRoot_someW

/-- info: 'LeanVM.Guest.B1.Sig.verify_someW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.verify_someW

/-- info: 'LeanVM.Guest.B1.Sig.xDigest0_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.xDigest0_comp

/-- info: 'LeanVM.Guest.B1.Sig.xDigest1_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.xDigest1_comp

/-- info: 'LeanVM.Guest.B1.Sig.xTail_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.xTail_comp

/-- info: 'LeanVM.Guest.B1.Sig.xLayer0_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.xLayer0_comp

/-- info: 'LeanVM.Guest.B1.Sig.xLayer1_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.xLayer1_comp

/-- info: 'LeanVM.Guest.B1.Sig.verify_lean_xmss_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.verify_lean_xmss_comp

/-- info: 'LeanVM.Guest.B1.Sig.verify_lean_xmss_rel_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.verify_lean_xmss_rel_comp

/-- info: 'LeanVM.Guest.B1.Sig.verify_lean_xmss_rel_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.verify_lean_xmss_rel_of_comp

/-- info: 'LeanVM.Guest.B1.Sig.sHash_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sHash_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.sChainWalk_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sChainWalk_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.sRecoverChain_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sRecoverChain_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.sLeafHash_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sLeafHash_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.sOtsLeaf_someInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sOtsLeaf_someInv

/-- info: 'LeanVM.Guest.B1.Sig.sTreeFold_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sTreeFold_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.sMessageDigest_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sMessageDigest_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.sForestWalk_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sForestWalk_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.sChildRecover_someInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sChildRecover_someInv

/-- info: 'LeanVM.Guest.B1.Sig.sSubFold_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sSubFold_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.sTopFold_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sTopFold_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.sSuperHash_cellsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sSuperHash_cellsE

/-- info: 'LeanVM.Guest.B1.Sig.sCoordRecover_someInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sCoordRecover_someInv

/-- info: 'LeanVM.Guest.B1.Sig.sForestRecover_someInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sForestRecover_someInv

/-- info: 'LeanVM.Guest.B1.Sig.sVerify_someInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sVerify_someInv

/-- info: 'LeanVM.Guest.B1.Sig.sPro1_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sPro1_comp

/-- info: 'LeanVM.Guest.B1.Sig.sPrologue_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sPrologue_comp

/-- info: 'LeanVM.Guest.B1.Sig.sLanes_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sLanes_comp

/-- info: 'LeanVM.Guest.B1.Sig.sCounter_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sCounter_comp

/-- info: 'LeanVM.Guest.B1.Sig.sTail_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sTail_comp

/-- info: 'LeanVM.Guest.B1.Sig.verify_sig_lean_sphincs_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.verify_sig_lean_sphincs_comp

/-- info: 'LeanVM.Guest.B1.Sig.verify_sig_lean_sphincs_rel_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.verify_sig_lean_sphincs_rel_comp

/-- info: 'LeanVM.Guest.B1.Sig.verify_sig_lean_sphincs_rel_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.verify_sig_lean_sphincs_rel_of_comp
