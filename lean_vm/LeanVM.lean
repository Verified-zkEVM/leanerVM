import LeanVM.Protocol.LeanVM
import LeanVM.Guest.EndFinal
import LeanVM.Guest.EndFinalComplete
import LeanVM.Guest.EndKnow
import LeanVM.Guest.Batch.Children
import LeanVM.Guest.Batch.Rom
import LeanVM.E2E.Main

/-! The theorems: the verifier's, `LeanVM.KnowledgeSoundness` and `LeanVM.Completeness` (`LeanVM/Spec/Statement.lean`), and the deployed aggregation guest's: `AggregateSound` (what the outer verifier's acceptance establishes) and `GuestKnowledge` (`LeanVM/Spec/Guest.lean`), its witness read off the execution's memory by `LeanVM.Guest.End.decode`, with `decode_binds`; the recursion step `LeanVM.Guest.Batch.children_sound` and the batching in the random-oracle model `LeanVM.Guest.Batch.batch_rom`; `GuestSound` and `GuestCompleteWithin` (`LeanVM/Guest/End.lean`). The build fails if their axiom footprint ever grows beyond Lean's three standard axioms. -/

/-- info: 'LeanVM.knowledgeSoundness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.knowledgeSoundness_holds

/-- info: 'LeanVM.completeness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_holds

/-- info: 'LeanVM.Guest.End.guest_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_sound

/-- info: 'LeanVM.Guest.End.aggregate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound

/-- info: 'LeanVM.Guest.End.guest_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_complete

/-- info: 'LeanVM.Guest.End.aggregate_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_complete

/-- info: 'LeanVM.Guest.End.guest_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_knowledge

/-- info: 'LeanVM.Guest.End.aggregate_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_knowledge

/-- info: 'LeanVM.Guest.End.decode_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.decode_binds

/-- info: 'LeanVM.Guest.End.aggregate_sound_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound_outer

/-- info: 'LeanVM.Guest.Batch.children_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.children_sound

/-- info: 'LeanVM.Guest.Batch.batch_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rom

/-! **The end-to-end security of the aggregation** (`LeanVM/E2E/Main.lean`, `docs/roadmap/e2e-security.md` §8, decision E2E-15), about the deployed verifier `verifyAggregate`, in the random-oracle model with honest signers. **Unforgeable** (`unforgeable`): if the deployed aggregation is knowledge sound against an adversary with error `ε` (`KnowledgeSound`, the assumption: every signature claim of an accepted statement has a signature valid under the adversary's own hash answers), and its game makes at most `q` hash evaluations (`DHashEvals`), `verifyAggregate` run with the random oracle accepts a forged claim of an honest key with probability at most `ε + (n_s + n_x/2^23 + 4) · q / 2^127`, `ε + q / 2^106` at `2^20 + 2^20` keys (`unforgeable_deployed`); the game's verifier at BLAKE2s is `verifyAggregate` (`verifier_eq`). **Correct** (`correct`): the deployed honest prover's aggregate of a valid tree of any depth is accepted by `verifyAggregate`. Supporting results, in the idealized model with the non-succinct verifier V_I: `ideal_unforgeable` (`(n_s + n_x/2^23 + 4) · q / 2^127`, forged or unbacked DA claims), `ideal_correct` (`completeError`), `ideal_faithful` (S1), `sanity` (T7″). The chain's intermediate theorems are pinned in `tests/LeanVMTests/E2E/Pins.lean` (decision E2E-12). -/

/-- info: 'LeanVM.E2E.Main.unforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.unforgeable

/-- info: 'LeanVM.E2E.Main.unforgeable_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.unforgeable_deployed

/-- info: 'LeanVM.E2E.Main.verifier_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.verifier_eq

/-- info: 'LeanVM.E2E.Main.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.correct

/-- info: 'LeanVM.E2E.Main.ideal_unforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.ideal_unforgeable

/-- info: 'LeanVM.E2E.Main.ideal_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.ideal_correct

/-- info: 'LeanVM.E2E.Main.ideal_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.ideal_faithful

/-- info: 'LeanVM.E2E.Main.sanity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.sanity
