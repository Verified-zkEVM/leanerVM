import LeanVM.Guest.B1.Comp.Digest.ClaimListAtC
import LeanVM.Guest.B1.Comp.Digest.ChildListAtC

/-!
# Tests: the claim lists placed over a completeness model, their axioms

`claim_list_digest` and `child_claim_list_digest` complete in the uniform placed form over a
`CompModel` (`CompleteRelBS CM.sem`), their callees and `NodeAt.lean`'s node and loop lemmas under
any semantics, and the deployed placed lemmas recovered at `CompModel.deployed`, rest on Lean's
three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.Digest.completeAtS_nodeB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.completeAtS_nodeB

/-- info: 'LeanVM.Guest.B1.Digest.completeAtS_loopB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.completeAtS_loopB

/-- info: 'LeanVM.Guest.B1.Digest.clPreAtC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.clPreAtC_deployed

/-- info: 'LeanVM.Guest.B1.Digest.clScratchC_of_memL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.clScratchC_of_memL

/-- info: 'LeanVM.Guest.B1.Digest.cld_completeRelBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cld_completeRelBS

/-- info: 'LeanVM.Guest.B1.Digest.cld_completeRelB_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cld_completeRelB_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.cct_runB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cct_runB

/-- info: 'LeanVM.Guest.B1.Digest.cct_relB_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cct_relB_low

/-- info: 'LeanVM.Guest.B1.Digest.cct_completeAtBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cct_completeAtBS

/-- info: 'LeanVM.Guest.B1.Digest.ccw_runB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ccw_runB

/-- info: 'LeanVM.Guest.B1.Digest.ccw_relB_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ccw_relB_low

/-- info: 'LeanVM.Guest.B1.Digest.ccw_completeAtBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ccw_completeAtBS

/-- info: 'LeanVM.Guest.B1.Digest.l87_holdsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.l87_holdsB

/-- info: 'LeanVM.Guest.B1.Digest.l87_steps_lowC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.l87_steps_lowC

/-- info: 'LeanVM.Guest.B1.Digest.l87_iterBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.l87_iterBS

/-- info: 'LeanVM.Guest.B1.Digest.l87_completeAtBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.l87_completeAtBS

/-- info: 'LeanVM.Guest.B1.Digest.ccld_holds_zeroC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ccld_holds_zeroC

/-- info: 'LeanVM.Guest.B1.Digest.ccld_holds_posC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ccld_holds_posC

/-- info: 'LeanVM.Guest.B1.Digest.cclPreAtC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cclPreAtC_deployed

/-- info: 'LeanVM.Guest.B1.Digest.cclScratchC_of_memL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cclScratchC_of_memL

/-- info: 'LeanVM.Guest.B1.Digest.ccld_completeRelBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ccld_completeRelBS

/-- info: 'LeanVM.Guest.B1.Digest.ccld_completeRelB_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ccld_completeRelB_of_comp
