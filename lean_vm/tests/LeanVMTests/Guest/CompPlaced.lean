import LeanVM.Guest.B1.Comp.CompleteAtB
import LeanVM.Guest.B1.Comp.Sig.CompleteAtC
import LeanVM.Guest.B1.Comp.Digest.SmallAtC
import LeanVM.Guest.B1.Comp.VerifySub.Assemble

/-!
# Tests: the placed form over any semantics, the placed verifiers and small callees, and
`verify_sub`'s assembly over a completeness model, their axioms

The semantics-generic placed layer (`CompleteAtBS`: straight, flat and one-branch bodies, pure
functions on agreeing memories), the signature verifiers and `statement_digest`, `da_list_digest`,
`cover_da_root` placed over a `CompModel` (`CompleteRelBS CM.sem`), `verify_sub`'s body and relation
over a `CompModel` at a model run record, and the deployed lemmas recovered from them at
`CompModel.deployed`, rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.completeAtBS_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtBS_deployed

/-- info: 'LeanVM.Guest.B1.completeRelBS_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeRelBS_deployed

/-- info: 'LeanVM.Guest.B1.completeAtS_straightB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_straightB

/-- info: 'LeanVM.Guest.B1.completeAtS_flatB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_flatB

/-- info: 'LeanVM.Guest.B1.completeAtS_flatOutB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_flatOutB

/-- info: 'LeanVM.Guest.B1.completeAtS_iteB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_iteB

/-- info: 'LeanVM.Guest.B1.completeAtS_of_rel_lowB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_of_rel_lowB

/-- info: 'LeanVM.Guest.B1.Sig.lowLin_relAtInBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.lowLin_relAtInBS

/-- info: 'LeanVM.Guest.B1.Sig.xmss_relInB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.xmss_relInB

/-- info: 'LeanVM.Guest.B1.Sig.sphincs_relInB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sphincs_relInB

/-- info: 'LeanVM.Guest.B1.verify_lean_xmss_completeRelBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_lean_xmss_completeRelBS

/-- info: 'LeanVM.Guest.B1.verify_sig_lean_sphincs_completeRelBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_sig_lean_sphincs_completeRelBS

/-- info: 'LeanVM.Guest.B1.verify_lean_xmss_completeRelB_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_lean_xmss_completeRelB_of_comp

/-- info: 'LeanVM.Guest.B1.verify_sig_lean_sphincs_completeRelB_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_sig_lean_sphincs_completeRelB_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.completeRel_casesBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.completeRel_casesBS

/-- info: 'LeanVM.Guest.B1.Digest.sdPreAtC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.sdPreAtC_deployed

/-- info: 'LeanVM.Guest.B1.Digest.sd_completeRelBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.sd_completeRelBS

/-- info: 'LeanVM.Guest.B1.Digest.sd_completeRelB_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.sd_completeRelB_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.daListPreAtC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.daListPreAtC_deployed

/-- info: 'LeanVM.Guest.B1.Digest.dl_completeRelBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.dl_completeRelBS

/-- info: 'LeanVM.Guest.B1.Digest.dl_completeRelB_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.dl_completeRelB_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.cover_completeRelBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cover_completeRelBS

/-- info: 'LeanVM.Guest.B1.Digest.cover_completeRelB_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cover_completeRelB_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.VsRunC.ans_ofD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsRunC.ans_ofD

/-- info: 'LeanVM.Guest.B1.VerifySub.VsData.Ok.toOkC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsData.Ok.toOkC

/-- info: 'LeanVM.Guest.B1.VerifySub.VsMem0.toC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsMem0.toC

/-- info: 'LeanVM.Guest.B1.VerifySub.VsCallsFree.relB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsCallsFree.relB

/-- info: 'LeanVM.Guest.B1.VerifySub.VsCallsOk.toFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsCallsOk.toFree

/-- info: 'LeanVM.Guest.B1.VerifySub.VsCallsOk.toC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsCallsOk.toC

/-- info: 'LeanVM.Guest.B1.VerifySub.VsCallsOkC.ofRelB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsCallsOkC.ofRelB

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_bodyC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_bodyC

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_complete_relC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_complete_relC

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_body_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_body_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_rel_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_rel_of_comp
