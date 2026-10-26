import LeanVM.Protocol.LeanVM
import LeanVM.Protocol.LeanVMRpm
import LeanVM.Guest.Batch.Children
import LeanVM.Guest.Batch.Rpm
import LeanVM.Guest.EndRpm
import LeanVM.Guest.Budget.ClosedN
import LeanVM.Guest.Budget.Covered
import LeanVM.Guest.Child.End
import XmssSecurity.Rpm
import Sphincs.LifetimesRpm
import LeanDa
import Statement.Theorems
import Statement.Corollaries

/-! # The end theorems of leanVM

`LeanVM.theorems_hold` (at the end) proves `Statement.Theorems` (`Statement/Theorems.lean`): every end
statement of the repository, leanXMSS's, leanSPHINCS's and LeanDA's included, in one theorem.
`LeanVM.corollaries_of_theorems` proves `Statement.Corollaries` (`Statement/Corollaries.lean`) from
the fields of `Statement.Theorems` alone, and `LeanVM.corollaries_hold` for the decoder
`LeanVM.Guest.End.decode`.

Each proves a proposition of `Statement/` (`Statement/README.md`), in the random-permutation model
where an adversary is involved:

* `LeanVM.knowledgeSoundness_holds : KnowledgeSoundness` and `LeanVM.completeness_holds :
  Completeness` (`Statement/LeanVm.lean`): the verifier, knowledge sound for the fixed straight-line extractor
  and complete;
* `LeanVM.Guest.End.guest_knowledge : GuestKnowledge guest decode` and
  `LeanVM.Guest.Binding.digest_binds : DigestBinds` (`Statement/LeanVmGuest.lean`; with
  `knowledgeSoundness_holds` they compose to `LeanVM.Guest.End.aggregate_sound_outer :
  AggregateSound guest decode`, `Statement/Corollaries.lean`): the leanISA guest program, its
  witness named by the decoder
  `LeanVM.Guest.End.decode` (`LeanVM/Guest/EndFinal.lean`; the propositions hold of any decoder
  that outputs valid witnesses, their content is in the decoder the theorems name);
* `LeanVM.Guest.Budget.guest_complete_covered : GuestCompleteCovered` (`Statement/LeanVmGuest.lean`;
  `guest_complete_recursion : GuestCompleteRecursion` and `guest_complete_leaf : GuestCompleteLeaf`,
  `Statement/Corollaries.lean`, are its first two families): the guest program's completeness on
  the covered nodes;
* `LeanVM.Guest.Budget.guest_child_complete : GuestChildComplete` (`Statement/LeanVmGuest.lean`):
  the honest proof of a guest execution is a child the guest accepts (rejected with probability
  at most `2^-126` in the random-permutation model; with the deployed Keccak, where accepted,
  meeting every hypothesis the guest's completeness assumes of a child);
* `LeanVM.Guest.Batch.batch_sound_holds : BatchSound` (`Statement/LeanVmGuest.lean`): the
  recursion step, the batching of the children's deferred claims run outside the circuit, sound in
  the random-permutation model (from `batch_rpm`).

The other theorems pinned below are steps or corollaries: the bounds' numbers, the guest's batching
of its children's deferred claims (`LeanVM.Guest.Batch.children_sound`, and in the
random-permutation model `batch_rpm`, `batch_rpm_bits`), `decode_binds`, `guest_sound`,
`aggregate_knowledge`, and the guest's completeness within its deployed budget
(`LeanVM.Guest.Budget.guest_complete`, `guest_complete_numeric`).
The two-oracle random-oracle model the proofs pass through (`LeanVM/Protocol/Rom/Statement.lean`:
`LeanVM.knowledgeSoundnessRom_holds`, `LeanVM.completenessRom_holds`; the batching's
`LeanVM.Guest.Batch.batch_rom`, `batch_rom_bits`) is a proof step: its theorems are not pinned here
(`tests/LeanVMTests/Protocol/` and `tests/LeanVMTests/Guest/Batch.lean` check their footprints).
The build fails if their axiom footprint ever grows beyond Lean's three standard axioms. -/

example : LeanVM.KnowledgeSoundness := LeanVM.knowledgeSoundness_holds
example : LeanVM.Completeness := LeanVM.completeness_holds
example : LeanVM.Node.GuestKnowledge LeanVM.Guest.guest LeanVM.Guest.End.decode :=
  LeanVM.Guest.End.guest_knowledge
example : LeanVM.Node.DigestBinds := LeanVM.Guest.Binding.digest_binds
example : LeanVM.Node.AggregateSound LeanVM.Guest.guest LeanVM.Guest.End.decode :=
  LeanVM.Guest.End.aggregate_sound_outer
example : LeanVM.Guest.Budget.GuestCompleteRecursion := LeanVM.Guest.Budget.guest_complete_recursion
example : LeanVM.Guest.Budget.GuestCompleteLeaf := LeanVM.Guest.Budget.guest_complete_leaf
example : LeanVM.Guest.Budget.GuestCompleteCovered := LeanVM.Guest.Budget.guest_complete_covered
example : LeanVM.Guest.Budget.GuestChildComplete := LeanVM.Guest.Budget.guest_child_complete
example : LeanVM.Guest.Batch.BatchSound := LeanVM.Guest.Batch.batch_sound_holds

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

/-- info: 'LeanVM.completenessError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completenessError_le

/-- info: 'LeanVM.completeness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_holds

/-- info: 'LeanVM.Rpm.soundnessRpm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Rpm.soundnessRpm_le

/-- info: 'LeanVM.Rpm.soundnessRpm_le_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Rpm.soundnessRpm_le_bits

/-- info: 'LeanVM.Rpm.completenessRpm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Rpm.completenessRpm_le

/-- info: 'LeanVM.keccak256_eq_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.keccak256_eq_rpm

/-- info: 'LeanVM.Guest.Batch.children_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.children_sound

/-- info: 'LeanVM.Guest.Batch.batch_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rpm

/-- info: 'LeanVM.Guest.Batch.batch_rpm_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rpm_bits

/-- info: 'LeanVM.Guest.Batch.batch_sound_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_sound_holds

/-- info: 'LeanVM.Guest.End.guest_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_knowledge

/-- info: 'LeanVM.Guest.End.decode_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.decode_binds

/-- info: 'LeanVM.Guest.Binding.digest_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Binding.digest_binds

/-- info: 'LeanVM.Guest.End.aggregate_sound_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound_outer

/-- info: 'LeanVM.Guest.End.aggregate_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_knowledge

/-- info: 'LeanVM.Guest.End.aggregate_complete_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_complete_of

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

/-- info: 'LeanVM.Guest.Budget.guest_complete_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guest_complete_covered

/-- info: 'LeanVM.Guest.Budget.guest_child_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guest_child_complete

/-- **Every end theorem**, `Statement/Theorems.lean`, the guest's witness named by
`LeanVM.Guest.End.decode`. -/
theorem LeanVM.theorems_hold : Statement.Theorems LeanVM.Guest.End.decode where
  knowledgeSoundness := LeanVM.knowledgeSoundness_holds
  completeness := LeanVM.completeness_holds
  guestKnowledge := LeanVM.Guest.End.guest_knowledge
  digestBinds := LeanVM.Guest.Binding.digest_binds
  guestCompleteCovered := LeanVM.Guest.Budget.guest_complete_covered
  guestChildComplete := LeanVM.Guest.Budget.guest_child_complete
  batchSound := LeanVM.Guest.Batch.batch_sound_holds
  leanXmss := XmssSecurity.leanXmss_rpm_security
  leanSphincs := Sphincs.Lifetimes.requestedSecurityRpm
  leanDaComplete := LeanDa.leanDa_perfectlyComplete_rpm
  leanDaPositionBinding := LeanDa.leanDa_positionBinding_rpm
  leanDaCodeBinding := LeanDa.leanDa_codeBinding_rpm_bound

/-- info: 'LeanVM.theorems_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.theorems_hold

open OracleComp in
/-- **The corollaries follow from the end theorems**, field by field: `aggregateSound` from
`knowledgeSoundness`, `guestKnowledge` and `digestBinds` (an accepted proof whose extracted
execution decodes, by `guestKnowledge`, to a statement of the accepted digest, which `digestBinds`
identifies with the accepted statement or turns into a collision), the completeness on recursion
nodes and leaves from `guestCompleteCovered` (the first two families of `Covered`). -/
theorem LeanVM.corollaries_of_theorems {decode : LeanVM.Node.Decoder}
    (h : Statement.Theorems decode) : Statement.Corollaries decode where
  aggregateSound := by
    intro A Q hA hQ
    refine le_trans (prEvent_mono _ _ _ ?_) (h.knowledgeSoundness A Q hA hQ)
    rintro ⟨⟨⟨⟨prog, input⟩, π⟩, b⟩, T⟩ ⟨s, hb, hprog, hpub, hs, hno⟩
    dsimp only [LeanVM.RpmOutcome.program] at hprog
    subst hprog
    refine ⟨hb, ?_⟩
    rintro ⟨t, hx, hv⟩
    obtain ⟨hd, hrel⟩ := h.guestKnowledge input t hv
    refine hno ⟨t, hx, ?_⟩
    rcases h.digestBinds _ _ _ _ _ hrel.1 hs (hd.trans hpub) with ⟨h1, h2⟩ | hc
    · exact Or.inl ⟨h1, h2, h1 ▸ h2 ▸ hrel⟩
    · exact Or.inr hc
  guestCompleteRecursion := by
    intro seed s w hrel hlim hcap hnz hx hs hd hdecl hcov hkids
    refine h.guestCompleteCovered seed s w hrel hlim hcap hnz ?_
    simp only [LeanVM.Guest.Budget.Covered]
    exact Or.inl ⟨by omega, hd, hdecl, hcov, hkids⟩
  guestCompleteLeaf := by
    intro seed s w hrel hlim hcap hnz hch hd hraw hdecl hcov
    refine h.guestCompleteCovered seed s w hrel hlim hcap hnz ?_
    simp only [LeanVM.Guest.Budget.Covered]
    exact Or.inr (Or.inl ⟨by simp [hch], hd, hraw, hdecl, hcov⟩)

/-- info: 'LeanVM.corollaries_of_theorems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.corollaries_of_theorems

/-- **Every corollary**, `Statement/Corollaries.lean`, the guest program's witness named by
`LeanVM.Guest.End.decode`. -/
theorem LeanVM.corollaries_hold : Statement.Corollaries LeanVM.Guest.End.decode :=
  LeanVM.corollaries_of_theorems LeanVM.theorems_hold

/-- info: 'LeanVM.corollaries_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.corollaries_hold
