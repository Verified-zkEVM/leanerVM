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

/-! **The end-to-end security of the aggregation** (`LeanVM/E2E/Main.lean`, `docs/roadmap/e2e-security.md` §8): in the random-oracle model with honest signers, the idealized verifier V_I on at most `N` nodes with the budget `viCost N` accepts a forged claim of an honest key or an unbacked DA claim with probability at most `q · 2^-λ₁ + 30 q²/2^256` (`no_forgery`; `q` every hash evaluation of the game, `λ₁ = 106` at `2^20 + 2^20` keys), and at most `q · 2^-116 + 2^34 q²/2^256` with leanSPHINCS's sharp bound at the deployed sets `full` and `pruned20` (`no_forgery_sharp`, `no_forgery_sharp_deployed`); the honest prover's proof is rejected by the same V_I with probability at most `completeError` (`complete`), for trees of aggregation nodes of any depth too (`complete_recursive`); V_I with BLAKE2s accepts what the deployed aggregation accepts, the reached stacks known (`sanity`, T7″); the deployed honest aggregation is accepted by `verifyAggregate` and by V_I with BLAKE2s, unless a compression collision exists (`sanity_deployed`, S1). The chain's intermediate theorems are pinned in `tests/LeanVMTests/E2E/Pins.lean` (decision E2E-12). -/

/-- info: 'LeanVM.E2E.Main.no_forgery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.no_forgery

/-- info: 'LeanVM.E2E.Main.no_forgery_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.no_forgery_sharp

/-- info: 'LeanVM.E2E.Main.no_forgery_sharp_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.no_forgery_sharp_deployed

/-- info: 'LeanVM.E2E.sharp_full_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sharp_full_deployed

/-- info: 'LeanVM.E2E.sharp_pruned20_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sharp_pruned20_deployed

/-- info: 'LeanVM.E2E.Main.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.complete

/-- info: 'LeanVM.E2E.Main.complete_recursive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.complete_recursive

/-- info: 'LeanVM.E2E.Main.sanity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.sanity

/-- info: 'LeanVM.E2E.Main.sanity_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Main.sanity_deployed
