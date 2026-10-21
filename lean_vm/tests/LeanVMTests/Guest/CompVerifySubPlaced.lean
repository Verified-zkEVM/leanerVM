import LeanVM.Guest.B1.Comp.VerifySub.Placed

/-!
# Tests: `verify_sub` placed over a completeness model, its axioms

The trees of functions free of `BLAKE2S` under any semantics (`validB_freeOn`), `verify_sub`'s
hashing callees' placed shapes over a model, its path, callees and placed completeness within
weights over a `CompModel` at a run record, its node decoding the run, and the deployed
`verify_sub_completeAtW` recovered at `CompModel.deployed`, rest on Lean's three standard axioms
only.
-/

/-- info: 'LeanVM.Guest.Memory.validB_freeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.validB_freeOn

/-- info: 'LeanVM.Guest.Memory.relAtInB_freeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relAtInB_freeOn

/-- info: 'LeanVM.Guest.Memory.totalLeB_of_freeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.totalLeB_of_freeOn

/-- info: 'LeanVM.Guest.Memory.weightLeB_of_freeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.weightLeB_of_freeOn

/-- info: 'LeanVM.Guest.B1.completeAtBS_of_freeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtBS_of_freeOn

/-- info: 'LeanVM.Guest.B1.completeAtWS_of_freeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtWS_of_freeOn

/-- info: 'LeanVM.Guest.B1.completeAtWS_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtWS_deployed

/-- info: 'LeanVM.Guest.B1.relAtInWS_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.relAtInWS_deployed

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteGkrAtW.toC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteGkrAtW.toC

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteTablesAtW.toC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteTablesAtW.toC

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteFlockAtW.toC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteFlockAtW.toC

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteOpenAtB.toC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteOpenAtB.toC

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_runC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_runC

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_callsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_callsC

/-- info: 'LeanVM.Guest.B1.VerifySub.match1C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.match1C

/-- info: 'LeanVM.Guest.B1.VerifySub.matchOpenC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.matchOpenC

/-- info: 'LeanVM.Guest.B1.VerifySub.matchTermC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.matchTermC

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_allocsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_allocsC

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_loadC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_loadC

/-- info: 'LeanVM.Guest.B1.VerifySub.vsAll_memC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsAll_memC

/-- info: 'LeanVM.Guest.B1.VerifySub.vsBufsC_ofD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsBufsC_ofD

/-- info: 'LeanVM.Guest.B1.VerifySub.vsExtLC_ofD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsExtLC_ofD

/-- info: 'LeanVM.Guest.B1.VerifySub.vsKids1_completeWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsKids1_completeWC

/-- info: 'LeanVM.Guest.B1.VerifySub.vsOpenKid_completeWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsOpenKid_completeWC

/-- info: 'LeanVM.Guest.B1.VerifySub.vsTermKid_completeWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsTermKid_completeWC

/-- info: 'LeanVM.Guest.B1.VerifySub.relAtInWS_of_walk_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.relAtInWS_of_walk_root

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteAtWSRoot.toWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteAtWSRoot.toWS

/-- info: 'LeanVM.Guest.B1.VerifySub.stream_lengthC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.stream_lengthC

/-- info: 'LeanVM.Guest.B1.VerifySub.vsDecodes_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsDecodes_of

/-- info: 'LeanVM.Guest.B1.VerifySub.vsProofOf_of_decodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsProofOf_of_decodes

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWC

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWSC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWSC

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWRoot_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWRoot_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_completeAtW_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_completeAtW_of_comp
