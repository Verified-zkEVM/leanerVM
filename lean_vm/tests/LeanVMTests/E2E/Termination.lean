import LeanVM.E2E.Termination

/-!
# Tests: termination (T3)

* The end lemmas of T3 rest on Lean's three axioms.
* **The guest's offset**: the last matrix coordinate of a deferred claim of the guest's shape
  sits at byte `96 + 24 · (22 + 28) = 1296` of its statement bytes.
* The empty log has no prediction; a log whose one entry's input carries its own answer's
  challenge at the offset is a prediction (the self-prediction `j = i`).
* Following on a chain is reflexive.
-/

namespace LeanVMTests.E2E.Termination

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Node LeanVM.E2E

/-- info: 'LeanVM.E2E.rank_lt_of_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rank_lt_of_child

/-- info: 'LeanVM.E2E.prEvent_game_pred_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_game_pred_le

/-- info: 'LeanVM.E2E.prEvent_game_pred_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_game_pred_le_sq

/-- info: 'LeanVM.E2E.predPot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms predPot_step

/-- info: 'LeanVM.E2E.slice_stmtInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slice_stmtInput

/-- The guest's prediction offset is byte `1296`. -/
example : predOffset (LeanVM.bytecodeWords LeanVM.Guest.guest) = 1296 := by
  rw [predOffset, show (LeanVM.bytecodeWords LeanVM.Guest.guest).length = 2 ^ 22 from
    LeanVM.Guest.End.bytecode_length, Nat.log2_two_pow]
  rfl

/-- The empty log has no prediction. -/
example (o : ℕ) : ¬ Pred o [] := not_pred_nil o

/-- An entry carrying its own answer's challenge at the offset is a prediction. -/
example (o : ℕ) (u : Digest) :
    Pred o [(List.replicate o 0 ++ eBytes (challengeOf u), u)] := by
  refine ⟨0, by simp, 0, le_rfl, ?_⟩
  simp only [List.getElem_cons_zero]
  rw [List.drop_left' (by simp), List.take_of_length_le (by rfl)]

/-- Following on a chain is reflexive. -/
example (ℓ : Log) (d : Digest) : ChainLE ℓ d d := ChainLE.refl ℓ d

/-- The potential of the empty log is the whole budget `N (N + 1) / 2^193`. -/
example (o N : ℕ) : predPot o N [] = N * (N + 1) / 2 ^ 193 := predPot_nil o N

end LeanVMTests.E2E.Termination
