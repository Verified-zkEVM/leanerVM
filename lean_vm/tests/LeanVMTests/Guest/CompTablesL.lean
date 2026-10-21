import LeanVM.Guest.B1.Comp.Tables.CalleesCL

/-!
# Tests: the tables' placed forms loading what they read, their axioms

`verify_bus_gkr`, `verify_tables` and `verify_flock` placed over a completeness model, their trees
loading the stream words they read (`CompleteGkrAtWCL`, `CompleteTablesAtWCL`,
`CompleteFlockAtWCL`), and the lemmas they rest on, rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.completeAtS_straightWT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_straightWT

/-- info: 'LeanVM.Guest.B1.completeAtS_flatWT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_flatWT

/-- info: 'LeanVM.Guest.B1.vtcS_completeAt_iteWT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.vtcS_completeAt_iteWT

/-- info: 'LeanVM.Guest.B1.CompleteAtWS.toWST_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.CompleteAtWS.toWST_of_valid

/-- info: 'LeanVM.Guest.B1.loopStdS_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.loopStdS_loads

/-- info: 'LeanVM.Guest.B1.l82_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.l82_loads

/-- info: 'LeanVM.Guest.B1.verify_flock_completeAtWCL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_flock_completeAtWCL

/-- info: 'LeanVM.Guest.B1.VerifySub.sr5_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.sr5_loads

/-- info: 'LeanVM.Guest.B1.VerifySub.l101_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.l101_loads

/-- info: 'LeanVM.Guest.B1.VerifySub.l10_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.l10_loads

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_bus_gkr_completeAtWCL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_bus_gkr_completeAtWCL

/-- info: 'LeanVM.Guest.B1.VerifySub.sr4_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.sr4_loads

/-- info: 'LeanVM.Guest.B1.VerifySub.l79_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.l79_loads

/-- info: 'LeanVM.Guest.B1.VerifySub.vtKids_loop79' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vtKids_loop79

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_tables_completeAtWCL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_tables_completeAtWCL

/-- info: 'LeanVM.Guest.B2C.gkrCL_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.gkrCL_b2c

/-- info: 'LeanVM.Guest.B2C.tablesCL_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.tablesCL_b2c

/-- info: 'LeanVM.Guest.B2C.flockCL_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.flockCL_b2c
