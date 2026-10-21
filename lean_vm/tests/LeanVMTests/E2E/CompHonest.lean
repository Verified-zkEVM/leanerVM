import LeanVM.E2E.Complete.HonestVs

/-!
# Tests: the honest bodies under the honest run's table (T6-det, L9's honest frames)

The positional facts of the completeness walk (`B2C.honest_onRun`, `B2C.instKB_kids`,
`B2C.cplRunKB_all`), the hash model of a functional semantics (`HashModel.ofFunctional`), the
contracts and bodies under the honest run's table (`honest_contracts`, `honest_bodyAt`,
`honest_bodyAt_plain`, `honest_main_bodyAt`) and `verify_sub`'s (`honest_exp_root`,
`honest_exp_loop`, `honest_vs_bodyAt`) rest on Lean's three axioms.
-/

namespace LeanVMTests.E2E.CompHonest

/-- info: 'LeanVM.Guest.B2C.cplRunKB_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.cplRunKB_all

/-- info: 'LeanVM.Guest.B2C.cplKB_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.cplKB_run

/-- info: 'LeanVM.Guest.B2C.instKB_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.instKB_kids

/-- info: 'LeanVM.Guest.B2C.insts_induct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.insts_induct

/-- info: 'LeanVM.Guest.B2C.honest_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.honest_onRun

/-- info: 'LeanVM.Guest.B2C.walk_sites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.walk_sites

/-- info: 'LeanVM.E2E.Complete.HashModel.ofFunctional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.HashModel.ofFunctional

/-- info: 'LeanVM.E2E.Complete.safe_tableSem_of_segment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.safe_tableSem_of_segment

/-- info: 'LeanVM.E2E.Complete.honest_contracts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_contracts

/-- info: 'LeanVM.E2E.Complete.honest_bodyAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_bodyAt

/-- info: 'LeanVM.E2E.Complete.honest_bodyAt_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_bodyAt_plain

/-- info: 'LeanVM.E2E.Complete.honest_main_bodyAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_main_bodyAt

/-- info: 'LeanVM.E2E.Complete.honest_frame_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_frame_val

/-- info: 'LeanVM.E2E.Complete.honest_exp_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_exp_root

/-- info: 'LeanVM.E2E.Complete.honest_exp_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_exp_loop

/-- info: 'LeanVM.E2E.Complete.honest_vs_bodyAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_vs_bodyAt

/-- info: 'LeanVM.E2E.Complete.honest_valAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_valAt

end LeanVMTests.E2E.CompHonest
