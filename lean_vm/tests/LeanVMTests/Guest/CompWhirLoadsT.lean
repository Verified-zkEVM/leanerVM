import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsStreamL
import LeanVM.Guest.B1.Comp.Whir.LoadsT.CapL

/-!
# Tests: `open_stacked` and `verify_merkle_cap` load what they read, their axioms

Every valid tree of an `open_stacked` specialization loads the `osStreamLen` stream words at its
cursor (`os_streamLoads`, through the templates' cursor tracking and the callees `opening_fold`
and `opening_final_message__L{n}`); a property of every valid tree joins a `CompleteAtBST`
(`CompleteAtBST.and_of_valid`); every valid tree of `verify_merkle_cap__L{cd}` loads the cap's
cells of the root and of every flagged node (`vmc_capLoads`). All rest on Lean's three standard
axioms only.
-/

/-- info: 'LeanVM.Guest.B1.osL_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osL_fold

/-- info: 'LeanVM.Guest.B1.osL_fm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osL_fm

/-- info: 'LeanVM.Guest.B1.osL_validB_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osL_validB_read

/-- info: 'LeanVM.Guest.B1.osL_kidOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osL_kidOf

/-- info: 'LeanVM.Guest.B1.osL_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osL_level

/-- info: 'LeanVM.Guest.B1.osL_levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osL_levels

/-- info: 'LeanVM.Guest.B1.osL_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osL_head

/-- info: 'LeanVM.Guest.B1.osL_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osL_tail

/-- info: 'LeanVM.Guest.B1.osStreamLen_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osStreamLen_eq

/-- info: 'LeanVM.Guest.B1.osL_fmOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osL_fmOk

/-- info: 'LeanVM.Guest.B1.osL_bodyFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osL_bodyFacts

/-- info: 'LeanVM.Guest.B1.os_streamLoadsCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_streamLoadsCfg

/-- info: 'LeanVM.Guest.B1.os_streamLoadsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_streamLoadsA

/-- info: 'LeanVM.Guest.B1.os_streamLoads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_streamLoads

/-- info: 'LeanVM.Guest.B1.CompleteAtBST.and_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.CompleteAtBST.and_of_valid

/-- info: 'LeanVM.Guest.B1.vmcL_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.vmcL_walk

/-- info: 'LeanVM.Guest.B1.vmcL_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.vmcL_side

/-- info: 'LeanVM.Guest.B1.vmcL_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.vmcL_loop

/-- info: 'LeanVM.Guest.B1.vmc_capLoads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.vmc_capLoads
