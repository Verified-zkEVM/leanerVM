import LeanVM.Guest.B1.Comp.VerifySub.Tail
import LeanVM.Guest.B1.Comp.VerifySub.Ring

/-!
# Tests: `verify_sub`'s blocks over a completeness model, their axioms

The completeness of `verify_sub`'s blocks over a `CompModel` (`LeanVM.Guest.B1.Comp.VerifySub`),
the hash-free blocks under any semantics, and the deployed completeness lemmas recovered from them
at `CompModel.deployed`, rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.keep

/-- info: 'LeanVM.Guest.B1.VerifySub.completesB_fsNextT_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.completesB_fsNextT_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.completes_fsNextT_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.completes_fsNextT_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.completesB_squeezeT_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.completesB_squeezeT_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.completes_squeezeT_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.completes_squeezeT_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.obsAllM_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.obsAllM_append

/-- info: 'LeanVM.Guest.B1.VerifySub.obsAllM_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.obsAllM_take

/-- info: 'LeanVM.Guest.B1.VerifySub.obsAllM_take_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.obsAllM_take_succ

/-- info: 'LeanVM.Guest.B1.VerifySub.completesB_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.completesB_step

/-- info: 'LeanVM.Guest.B1.VerifySub.completesB_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.completesB_last

/-- info: 'LeanVM.Guest.B1.VerifySub.c_seed_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_seed_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_seed_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_seed_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_read_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_read_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_read_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_read_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_reads_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_reads_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_reads_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_reads_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_sizesB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_sizesB

/-- info: 'LeanVM.Guest.B1.VerifySub.c_sizes_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_sizes_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_kbaseB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_kbaseB

/-- info: 'LeanVM.Guest.B1.VerifySub.c_bkBlkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_bkBlkB

/-- info: 'LeanVM.Guest.B1.VerifySub.c_blockKappaB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_blockKappaB

/-- info: 'LeanVM.Guest.B1.VerifySub.c_pushBlk0B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_pushBlk0B

/-- info: 'LeanVM.Guest.B1.VerifySub.c_pushBlkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_pushBlkB

/-- info: 'LeanVM.Guest.B1.VerifySub.c_pushB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_pushB

/-- info: 'LeanVM.Guest.B1.VerifySub.c_push_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_push_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_root_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_root_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_root_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_root_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.sqAllM_states' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.sqAllM_states

/-- info: 'LeanVM.Guest.B1.VerifySub.c_squeezes_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_squeezes_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_squeezes_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_squeezes_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_eqwEntryB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_eqwEntryB

/-- info: 'LeanVM.Guest.B1.VerifySub.c_bus_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_bus_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_bus_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_bus_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_callsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_callsB

/-- info: 'LeanVM.Guest.B1.VerifySub.c_calls_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_calls_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_lam_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_lam_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_lam_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_lam_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_openB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_openB

/-- info: 'LeanVM.Guest.B1.VerifySub.c_open_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_open_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_deferB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_deferB

/-- info: 'LeanVM.Guest.B1.VerifySub.c_defer_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_defer_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_ctSlotG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_ctSlotG

/-- info: 'LeanVM.Guest.B1.VerifySub.c_ctStageG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_ctStageG

/-- info: 'LeanVM.Guest.B1.VerifySub.rsSumC_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.rsSumC_target

/-- info: 'LeanVM.Guest.B1.VerifySub.c_ring_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_ring_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.c_ring_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.c_ring_of_comp
