import LeanVM.Guest.B1.Comp.VsInv.Field

/-!
# Tests: `verify_sub`'s inversion over a completeness model, its axioms

The deferring verifier's runs over a hash model inverted (the elementary runs, the frames, the
phases, the tables' claims), the inversion of an accepting `verifyDeferredWith CM.H` into a run
with a run record of the model's answers within the limits over the model (`vs_inversionC`), the
opening's caps from the run's over a total hash (`deferredCapsC`), the `vs_inv` field of
`B1CompHyps` (`vs_invC`, at `CapAgreesC CM`), and the deployed inversion and field recovered at
`CompModel.deployed`, rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.VerifySub.RunsM.bind_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.RunsM.bind_inv

/-- info: 'LeanVM.Guest.B1.VerifySub.RunsM.readN_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.RunsM.readN_inv

/-- info: 'LeanVM.Guest.B1.VerifySub.RunsM.sampleN_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.RunsM.sampleN_inv

/-- info: 'LeanVM.Guest.B1.VerifySub.runs_frameM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.runs_frameM

/-- info: 'LeanVM.Guest.B1.VerifySub.qfree_frameM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.qfree_frameM

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_flock_invM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_flock_invM

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_gkr_invM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_gkr_invM

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_tables_invM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_tables_invM

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_readSizes_invM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_readSizes_invM

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_announcedM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_announcedM

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_commitStack_invM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_commitStack_invM

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_ringSwitch_invM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_ringSwitch_invM

/-- info: 'LeanVM.Guest.B1.VerifySub.verifyDeferredWith_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verifyDeferredWith_inv

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_tablesSeg_invM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_tablesSeg_invM

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_tablesSeg_claimsOkM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_tablesSeg_claimsOkM

/-- info: 'LeanVM.Guest.B1.VerifySub.whirOpen_point_lengthM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.whirOpen_point_lengthM

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_inversionC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_inversionC

/-- info: 'LeanVM.Guest.B1.VerifySub.capAgreesWith_blake2s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.capAgreesWith_blake2s

/-- info: 'LeanVM.Guest.B1.VerifySub.capAgreesC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.capAgreesC_deployed

/-- info: 'LeanVM.Guest.B1.VerifySub.queriesOfW_with' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.queriesOfW_with

/-- info: 'LeanVM.Guest.B1.VerifySub.deferredCapsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.deferredCapsC

/-- info: 'LeanVM.Guest.B1.VerifySub.sqAllM_of_states' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.sqAllM_of_states

/-- info: 'LeanVM.Guest.B1.VerifySub.freshShapedC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.freshShapedC

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_invC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_invC

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_invC_capAgreesC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_invC_capAgreesC

/-- info: 'LeanVM.Guest.B1.VerifySub.VsRunC.Ans.eq_ofD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsRunC.Ans.eq_ofD

/-- info: 'LeanVM.Guest.B1.VerifySub.VsData.OkC.toOk_of_ans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsData.OkC.toOk_of_ans

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_inversion_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_inversion_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_invC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_invC_deployed
