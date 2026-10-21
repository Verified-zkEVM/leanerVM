import LeanVM.E2E.Knowledge

/-!
# Tests: aggregate knowledge (T4)

* The end lemmas of T4 rest on Lean's three axioms.
* **Non-vacuity of the bad events**: the empty log has none of them (`¬ AggBad []`).
* The deployed DA padding digests are the guest's baked ones.
-/

namespace LeanVMTests.E2E.Knowledge

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.EndToEnd.Blind LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Node LeanVM.E2E

/-- info: 'LeanVM.E2E.aggregate_knowledge_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_knowledge_cache

/-- info: 'LeanVM.E2E.aggregate_knowledge_cache'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_knowledge_cache'

/-- info: 'LeanVM.E2E.heldDirect_of_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms heldDirect_of_node

/-- info: 'LeanVM.E2E.prEvent_game_aggregate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_game_aggregate_le

/-- info: 'LeanVM.E2E.prEvent_game_aggBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_game_aggBad_le

/-- info: 'LeanVM.E2E.mem_blindCandidates_of_extractedBlind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_blindCandidates_of_extractedBlind

/-- info: 'LeanVM.E2E.nodeStep_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeStep_some

/-- info: 'LeanVM.E2E.statement_eq_of_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms statement_eq_of_digest

/-- The empty log has none of the chain's bad events. -/
example : ¬ AggBad [] := by
  rintro (h | h | h | h | h)
  · rw [pot_nil] at h
    exact absurd h (by simp)
  · exact not_fail_nil _ h
  · rw [BatchBad, batchPot_nil] at h
    exact absurd h (by simp)
  · rcases h with h | ⟨i, hi, -⟩
    · exact not_failDA_nil _ h
    · simp at hi
  · exact not_pred_nil _ h

/-- The deployed DA padding digests are the guest's. -/
example : deployedPads = (LeanVM.Guest.B1.Main.daPadCell, LeanVM.Guest.B1.Main.daPadRow) :=
  deployedPads_eq

end LeanVMTests.E2E.Knowledge
