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

/-! **The end-to-end security of the aggregation** (`LeanVM/E2E/Main.lean`, `docs/roadmap/e2e-security.md` §8, decision E2E-14), the three properties of an aggregate signature scheme, in the random-oracle model with honest signers. **Unforgeable** (`unforgeable`): for every adversary whose game makes at most `q` hash evaluations (`HashEvals`), the idealized verifier V_I accepts a forged claim of an honest key or an unbacked DA claim with probability at most `(n_s + n_x/2^23 + 4) · q / 2^127`, `q / 2^106` at `2^20 + 2^20` keys (`unforgeable_deployed`), `q / 2^124` with leanXMSS keys only (`unforgeable_xmss`). **Correct** (`correct`): the honest prover's proof of a generated valid tree of any depth is rejected by the same V_I with probability at most `completeError`. **Faithful** (`faithful`, S1): the deployed honest aggregation is accepted by `verifyAggregate` and by V_I with BLAKE2s, unless a compression collision exists. Refinements: leanSPHINCS's sharp bound, `q / 2^116 + 2^34 q²/2^256` at the deployed sets `full` and `pruned20` (`unforgeable_sharp`, `unforgeable_sharp_deployed`); V_I with BLAKE2s accepts what the deployed aggregation accepts, the reached stacks known (`sanity`, T7″). The chain's intermediate theorems are pinned in `tests/LeanVMTests/E2E/Pins.lean` (decision E2E-12). -/

/-- info: 'LeanVM.E2E.Main.unforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.unforgeable

/-- info: 'LeanVM.E2E.Main.unforgeable_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.unforgeable_deployed

/-- info: 'LeanVM.E2E.Main.unforgeable_xmss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.unforgeable_xmss

/-- info: 'LeanVM.E2E.Main.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.correct

/-- info: 'LeanVM.E2E.Main.faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.faithful

/-- info: 'LeanVM.E2E.Main.unforgeable_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.unforgeable_sharp

/-- info: 'LeanVM.E2E.Main.unforgeable_sharp_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.unforgeable_sharp_deployed

/-- info: 'LeanVM.E2E.sharp_full_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sharp_full_deployed

/-- info: 'LeanVM.E2E.sharp_pruned20_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sharp_pruned20_deployed

/-- info: 'LeanVM.E2E.Main.sanity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.sanity
