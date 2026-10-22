import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsInj

/-!
# Tests: instance injectivity in the stacked opening's tree, its axioms

Every valid placed tree of an `open_stacked` specialization satisfies `OsInj` (`os_inj`): its
`opening_queries` instances and their loop helpers' iterations each have a pointer argument into
the tree's region (`osPtrIdx`) and are the only instances of their function on their arguments.
The static facts (`osInjZ_callsIn`, `osI_cfg`, `osI_oqLoop`) are kernel evaluations. All rest on
Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.osInjZ_callsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osInjZ_callsIn

/-- info: 'LeanVM.Guest.B1.osInjZ_notMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osInjZ_notMem

/-- info: 'LeanVM.Guest.B1.osI_cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_cfg

/-- info: 'LeanVM.Guest.B1.osI_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_loop

/-- info: 'LeanVM.Guest.B1.osI_openNames' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_openNames

/-- info: 'LeanVM.Guest.B1.osI_oqLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_oqLoop

/-- info: 'LeanVM.Guest.B1.osI_oqLoop_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_oqLoop_atoms

/-- info: 'LeanVM.Guest.B1.osI_oqNames' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_oqNames

/-- info: 'LeanVM.Guest.B1.osI_mem_instsKids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_mem_instsKids

/-- info: 'LeanVM.Guest.B1.osI_kidsGet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_kidsGet

/-- info: 'LeanVM.Guest.B1.osI_placedKidsGet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_placedKidsGet

/-- info: 'LeanVM.Guest.B1.osI_instsZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_instsZ

/-- info: 'LeanVM.Guest.B1.osI_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_chain

/-- info: 'LeanVM.Guest.B1.osI_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_q

/-- info: 'LeanVM.Guest.B1.osI_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osI_spec

/-- info: 'LeanVM.Guest.B1.os_injCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_injCfg

/-- info: 'LeanVM.Guest.B1.os_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.os_inj
