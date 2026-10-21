import LeanVM.E2E.Batch

/-!
# Tests: the batching leg in the random-oracle model

* The end lemmas of the batching leg rest on Lean's three axioms.
* **The constant start.** The log read from `s0` answers the label with `s0` and every chain
  input as the log; a fresh query at the label leaves it unchanged.
* The empty log has potential zero, so it is not batching-bad; the batching answered by the empty
  log defers nothing.
* **An answer equal to the constant start is a failure**: a log whose one answer is `s0` is
  batching-bad, the collision the constant start adds to `Fail`.
-/

namespace LeanVMTests.E2E.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Node LeanVM.E2E

/-- info: 'LeanVM.E2E.bytecodeHolds_of_batchWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecodeHolds_of_batchWith

/-- info: 'LeanVM.E2E.children_bytecodeHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms children_bytecodeHolds

/-- info: 'LeanVM.E2E.prEvent_game_childrenFalse_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_game_childrenFalse_le

/-- info: 'LeanVM.E2E.verifyDeferredWith_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verifyDeferredWith_shaped

/-- info: 'LeanVM.E2E.prEvent_game_batchBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_game_batchBad_le

/-- info: 'LeanVM.E2E.prEvent_game_batchFalse_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_game_batchFalse_le

/-- info: 'LeanVM.E2E.prEvent_game_batchFalse_le_of_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_game_batchFalse_le_of_costs

/-- info: 'LeanVM.E2E.batchPot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batchPot_step

/-- info: 'LeanVM.E2E.batchPot_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batchPot_nil

/-- info: 'LeanVM.E2E.runProof_bytecodeProg_of_batchWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runProof_bytecodeProg_of_batchWith

/-- info: 'LeanVM.E2E.bytecodeCert_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecodeCert_bound

/-- info: 'LeanVM.E2E.doomed_of_falseBytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms doomed_of_falseBytecode

/-- info: 'LeanVM.E2E.batch_sound_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batch_sound_bytecode

/-! ## The constant start -/

/-- The label's hash is `s0`. -/
example (s0 : Digest) (ℓ : Log) : look (startLog s0 ℓ) batchLabel = some s0 :=
  look_startLog_label s0 ℓ

/-- Even when the log has answered the label otherwise. -/
example (s0 u : Digest) : look (startLog s0 [(batchLabel, u)]) batchLabel = some s0 :=
  look_startLog_label s0 _

/-- A chain input is answered as the log answers it. -/
example (s0 c : Digest) (x : E) (ℓ : Log) :
    look (startLog s0 ℓ) (digestBytes c ++ blockOf x 1) = look ℓ (digestBytes c ++ blockOf x 1) :=
  look_startLog_chain s0 ℓ c x 1

/-- The count's absorb from `s0` is the seeding's last input. -/
example (s0 : Digest) (ℓ : Log) (n : Fin (2 ^ 64 - 1)) :
    (batchSeedsAll.seed n).run (look (startLog s0 ℓ)) =
      look ℓ (digestBytes s0 ++ blockOf (ofK (gpow n)) 1) :=
  seed_run_startLog s0 ℓ n

/-- A fresh query at the label changes nothing. -/
example (s0 u : Digest) (ℓ : Log) : startLog s0 (ℓ ++ [(batchLabel, u)]) = startLog s0 ℓ :=
  startLog_append_label s0 ℓ u

/-! ## The empty log -/

/-- The empty log has potential zero. -/
example (s0 : Digest) (bytecode : List K) : batchPot s0 bytecode [] = 0 := batchPot_nil s0 bytecode

/-- The empty log is not batching-bad. -/
example (s0 : Digest) (bytecode : List K) : ¬ BatchBad s0 bytecode [] := by
  rw [not_batchBad_iff, batchPot_nil]
  exact zero_lt_one

/-- The empty log answers no batching. -/
example (s0 : Digest) (cs : List ChildClaims) (h : BatchHints) :
    batchWith (look []) s0 cs h = none := rfl

/-! ## A collision with the constant start -/

/-- A one-entry bytecode has a power-of-two length. -/
theorem pow_one_word : ([0] : List K).length = 2 ^ Nat.log2 ([0] : List K).length := by
  decide

/-- **An answer equal to `s0` is batching-bad**: read from `s0`, it collides with the label's
entry. -/
example (s0 : Digest) (x : Bytes) (hx : x ≠ batchLabel) : BatchBad s0 [0] [(x, s0)] := by
  refine batchBad_of_fail pow_one_word
    ⟨1, by simp [startLog, hx], Or.inl ⟨(batchLabel, s0), ?_, ?_⟩⟩
  · simp [startLog, hx]
  · simp [startLog, hx]

/-- The empty input is not the label. -/
theorem nil_ne_label : ([] : Bytes) ≠ batchLabel := fun h ↦ by
  have := congrArg List.length h
  simp [LeanVM.Guest.Batch.batchLabel_length] at this

/-- **The obstruction**: the log itself does not fail when an answer equals the constant start;
only the log read from `s0` does. -/
example (s0 : Digest) : ¬ Fail batchSeedsAll [([], s0)] ∧ BatchBad s0 [0] [([], s0)] := by
  refine ⟨?_, batchBad_of_fail pow_one_word ⟨1, by simp [startLog, nil_ne_label.symm],
    Or.inl ⟨(batchLabel, s0), by simp [startLog, nil_ne_label.symm],
      by simp [startLog, nil_ne_label.symm]⟩⟩⟩
  rintro ⟨i, hi, hbad⟩
  simp only [List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff] at hi
  subst hi
  simp only [List.take_zero, List.getElem_cons_zero, BadEntry, List.not_mem_nil, false_and,
    exists_false, List.map_nil, List.mem_singleton, exists_eq_left, false_or] at hbad
  rcases hbad with h | h | h | ⟨a, ha, -⟩
  · have := congrArg List.length h
    simp [chunk0, digestBytes_length] at this
  · have := congrArg List.length h
    simp [chunk1, digestBytes_length] at this
  · obtain ⟨_, _, _, _, -, hf, -⟩ := h
    simp at hf
  · simp [LeanVM.Guest.Batch.batchSeeds] at ha

end LeanVMTests.E2E.Batch
