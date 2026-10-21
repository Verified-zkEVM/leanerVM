import LeanVM.Guest.B1.Comp.VerifySub.PlacedEq

/-!
# Tests: `verify_sub`'s child proof decoded on its tree's equations, its axioms

The transcript callees' placed shapes loading the words they read, `verify_sub` placed over a
completeness model by a tree whose node decodes the child proof's stream on every reader satisfying
the tree's load equations, and the child proof decoded there, rest on Lean's three standard
axioms only.
-/

/-- info: 'LeanVM.Guest.B1.VerifySub.wordsAt_of_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.wordsAt_of_loads

/-- info: 'LeanVM.Guest.B1.VerifySub.WordsAt.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.WordsAt.append

/-- info: 'LeanVM.Guest.B1.VerifySub.WordsAt.cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.WordsAt.cons

/-- info: 'LeanVM.Guest.B1.VerifySub.streamAt_of_wordsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.streamAt_of_wordsAt

/-- info: 'LeanVM.Guest.B1.VerifySub.eqns_of_mem_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.eqns_of_mem_kids

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteAtWST.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteAtWST.mono

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteAtWST.bmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteAtWST.bmono

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteAtBST.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteAtBST.mono

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteGkrAtWCL.toWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteGkrAtWCL.toWC

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteTablesAtWCL.toWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteTablesAtWCL.toWC

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteFlockAtWCL.toWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteFlockAtWCL.toWC

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteOpenAtBCL.toBCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteOpenAtBCL.toBCT

/-- info: 'LeanVM.Guest.B1.VerifySub.vsKids1_completeWCL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsKids1_completeWCL

/-- info: 'LeanVM.Guest.B1.VerifySub.vsOpenKid_completeWCL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsOpenKid_completeWCL

/-- info: 'LeanVM.Guest.B1.VerifySub.VsDecodes.toFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsDecodes.toFrame

/-- info: 'LeanVM.Guest.B1.VerifySub.vsProofOf_eq_proofE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsProofOf_eq_proofE

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_own_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_own_loads

/-- info: 'LeanVM.Guest.B1.VerifySub.mem_vsEvs_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.mem_vsEvs_of

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_own_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_own_words

/-- info: 'LeanVM.Guest.B1.VerifySub.kidsSat_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.kidsSat_get

/-- info: 'LeanVM.Guest.B1.VerifySub.stream_wordsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.stream_wordsAt

/-- info: 'LeanVM.Guest.B1.VerifySub.kidsValidB_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.kidsValidB_length

/-- info: 'LeanVM.Guest.B1.VerifySub.vsRootTreeE_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsRootTreeE_of

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWCE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWCE

/-- info: 'LeanVM.Guest.B1.VerifySub.loadEqns_of_mem_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.loadEqns_of_mem_kids
