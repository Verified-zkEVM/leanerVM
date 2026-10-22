import LeanVM.Guest.B1.Comp.Whir.LocT.OsHonest
import LeanVM.Guest.B1.Comp.VerifySub.PlacedEqO

/-!
# Tests: the opening's tree form at the honest memory, its axioms

The bridges from `open_stacked`'s tree form to the honest memory's decoding (the decoded callees
plain, `NodeAgree` across re-choosing, `KidsLink` from the honest instances; `Comp/Whir/LocT/OsHonest`)
and `verify_sub`'s tree with the opening located at its dispatch (`Comp/VerifySub/PlacedEqO`) rest
on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.osDec_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.osDec_plain

/-- info: 'LeanVM.Guest.B1.openName_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.openName_mem

/-- info: 'LeanVM.Guest.B1.nodeAgree_of_retemp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.nodeAgree_of_retemp

/-- info: 'LeanVM.Guest.B1.kidsLink_of_vagree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.kidsLink_of_vagree

/-- info: 'LeanVM.Guest.B1.callVals_retemp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.callVals_retemp

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWCEO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_completeAtWCEO

/-- info: 'LeanVM.Guest.B1.VerifySub.vsRootTreeEO_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsRootTreeEO_of

/-- info: 'LeanVM.Guest.B1.VerifySub.VsRootTreeEO.toE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsRootTreeEO.toE

/-- info: 'LeanVM.Guest.B1.VerifySub.kidsSat_atI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.kidsSat_atI
