import LeanVM.Protocol.LeanVM
import LeanVM.Protocol.LeanVMRpm
import LeanVM.Guest.Batch.Children
import LeanVM.Guest.Batch.Rom
import LeanVM.Guest.EndFinal
import LeanVM.Guest.Budget.ClosedN
import LeanVM.Guest.Budget.Covered

/-! The theorems: the verifier's, `LeanVM.KnowledgeSoundness` and `LeanVM.Completeness`
(`LeanVM/Spec/Statement.lean`), for leanVM at `main` (Keccak-256 and Keccak-f[1600] as
independent random oracles), `LeanVM.KnowledgeSoundnessRpm` and `LeanVM.CompletenessRpm`
(`LeanVM/Spec/Rpm.lean`: both built from one random permutation), and the guest's batching of its
children's deferred claims (`LeanVM.Guest.Batch.children_sound`, `batch_rom`, `batch_rom_bits`),
and the guest's soundness with its witness named (`LeanVM.Guest.End.guest_knowledge`,
`decode_binds`, `aggregate_sound_outer`, `aggregate_knowledge`, `guest_sound`:
`LeanVM.Node.GuestKnowledge` and `LeanVM.Node.AggregateSound`
of `LeanVM/Spec/Guest.lean` for the deployed bytecode and the decoder `LeanVM.Guest.End.decode`;
`guest_sentinelSafe`), and the guest's completeness within its deployed budget
(`LeanVM.Guest.Budget.guest_complete`, `guest_complete_numeric`), with what it covers
(`guest_complete_recursion`: every node of at most `16` children, `2048` declared claims,
coverage slots and children's claims, holding no signature or blob directly;
`guest_complete_leaf`: every leaf of at most `2048` raw signatures, declared claims and coverage
slots, holding no blob directly).
The build fails if their axiom footprint ever grows beyond Lean's three standard axioms. -/

/-- info: 'LeanVM.knowledgeSoundness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.knowledgeSoundness_holds

/-- info: 'LeanVM.candidates_ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.candidates_ncard_le

/-- info: 'LeanVM.soundnessError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.soundnessError_le

/-- info: 'LeanVM.soundnessError_le_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.soundnessError_le_bits

/-- info: 'LeanVM.knowledgeSoundness_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.knowledgeSoundness_bits

/-- info: 'LeanVM.completenessError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completenessError_le

/-- info: 'LeanVM.completeness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_holds

/-- info: 'LeanVM.knowledgeSoundnessRpm_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.knowledgeSoundnessRpm_holds

/-- info: 'LeanVM.Rpm.soundnessRpm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Rpm.soundnessRpm_le

/-- info: 'LeanVM.Rpm.soundnessRpm_le_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Rpm.soundnessRpm_le_bits

/-- info: 'LeanVM.knowledgeSoundnessRpm_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.knowledgeSoundnessRpm_bits

/-- info: 'LeanVM.completenessRpm_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completenessRpm_holds

/-- info: 'LeanVM.Rpm.completenessRpm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Rpm.completenessRpm_le

/-- info: 'LeanVM.keccak256_eq_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.keccak256_eq_rpm

/-- info: 'LeanVM.Guest.Batch.children_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.children_sound

/-- info: 'LeanVM.Guest.Batch.batch_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rom

/-- info: 'LeanVM.Guest.Batch.batch_rom_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rom_bits

/-- info: 'LeanVM.Guest.End.guest_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_knowledge

/-- info: 'LeanVM.Guest.End.decode_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.decode_binds

/-- info: 'LeanVM.Guest.End.aggregate_sound_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound_outer

/-- info: 'LeanVM.Guest.guest_sentinelSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.guest_sentinelSafe

/-- info: 'LeanVM.Guest.End.aggregate_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_knowledge

/-- info: 'LeanVM.Guest.End.guest_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_sound

/-- info: 'LeanVM.Guest.Budget.guest_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guest_complete

/-- info: 'LeanVM.Guest.Budget.guestComplete_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guestComplete_mono

/-- info: 'LeanVM.Guest.Budget.guest_complete_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guest_complete_numeric

/-- info: 'LeanVM.Guest.Budget.guest_complete_recursion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guest_complete_recursion

/-- info: 'LeanVM.Guest.Budget.guest_complete_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guest_complete_leaf
