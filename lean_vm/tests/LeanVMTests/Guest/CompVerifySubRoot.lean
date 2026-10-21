import LeanVM.Guest.B1.Comp.VerifySub.PlacedRoot

/-!
# Tests: placed trees with predicates, composed, and `verify_sub`'s tree decoding the run, their axioms

The placed forms keeping a predicate of the tree (`TreeRoot.lean`), their composition through the
callees, the opening's tree form, and `verify_sub` placed over a completeness model with its tree
decoding the run and its opening's tree satisfying the opening's predicate, rest on Lean's three
standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.RelAtInWST.toWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.RelAtInWST.toWS

/-- info: 'LeanVM.Guest.B1.CompleteAtWST.toWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.CompleteAtWST.toWS

/-- info: 'LeanVM.Guest.B1.CompleteAtWS.toWST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.CompleteAtWS.toWST

/-- info: 'LeanVM.Guest.B1.CompleteAtBS.toBST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.CompleteAtBS.toBST

/-- info: 'LeanVM.Guest.B1.CompleteAtBST.toBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.CompleteAtBST.toBS

/-- info: 'LeanVM.Guest.B1.CompleteAtBST.toWST_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.CompleteAtBST.toWST_weightLe

/-- info: 'LeanVM.Guest.B1.CompleteAtWST.wmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.CompleteAtWST.wmono

/-- info: 'LeanVM.Guest.B1.kidST_ofInW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.kidST_ofInW

/-- info: 'LeanVM.Guest.B1.kidsST_of_kidsFromInWT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.kidsST_of_kidsFromInWT

/-- info: 'LeanVM.Guest.B1.relAtInWST_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.relAtInWST_of_walk

/-- info: 'LeanVM.Guest.B1.kidsFromInWST_dend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.kidsFromInWST_dend

/-- info: 'LeanVM.Guest.B1.kidsFromInWST_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.kidsFromInWST_append

/-- info: 'LeanVM.Guest.B1.kidsFromInWST_of_kidsW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.kidsFromInWST_of_kidsW

/-- info: 'LeanVM.Guest.B1.kidsWST_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.kidsWST_of

/-- info: 'LeanVM.Guest.B1.kidsFromInWST_of_kidsBW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.kidsFromInWST_of_kidsBW

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteOpenAtBCT.toBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteOpenAtBCT.toBC

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteOpenAtBC.toBCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteOpenAtBC.toBCT

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteAtBST.placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteAtBST.placed

/-- info: 'LeanVM.Guest.B1.VerifySub.kidsSat_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.kidsSat_at

/-- info: 'LeanVM.Guest.B1.VerifySub.vsOpenKid_completeWCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsOpenKid_completeWCT

/-- info: 'LeanVM.Guest.B1.VerifySub.vsProofOf_eq_proof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsProofOf_eq_proof

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWCT

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWCT_toWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWCT_toWS

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWT_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWT_of_comp
