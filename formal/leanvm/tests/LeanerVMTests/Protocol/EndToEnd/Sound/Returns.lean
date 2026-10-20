import LeanerVM.Protocol.EndToEnd.Sound.Returns

/-!
# The return invariant's tests

* **Statement locks** of the bounds on the claims the bus and table phases and the public-input
  phase return.
* **The trust audit**: the bounds depend on `propext`, `Classical.choice` and `Quot.sound` only.
* **What is load-bearing**: the predicate constrains the returns (a program returning `3` does not
  return at most `2`), and a rejecting program satisfies every predicate.
-/

namespace LeanerVMTests.Protocol.EndToEnd.Sound.Returns

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Compile
open LeanerVM.Protocol.EndToEnd.Sound

/-! ## Statement locks -/

example (layout : LeanerVM.Protocol.Verifier.Layout) :
    RetOK (fun claims : List LeanerVM.Protocol.Verifier.ColumnClaim ↦ claims.length ≤ 227)
      ((LeanerVM.Protocol.Verifier.verifyBusBalance .computed layout).bind
        (LeanerVM.Protocol.Verifier.tablePhase layout)) :=
  retOK_busTable layout

example (layout : LeanerVM.Protocol.Verifier.Layout) (publicInput : Digest) :
    RetOK (fun claims : List LeanerVM.Protocol.Verifier.ColumnClaim ↦ claims.length ≤ 3)
      (LeanerVM.Protocol.Verifier.publicInputPhase layout publicInput) :=
  retOK_publicInputPhase layout publicInput

/-! ## The trust audit -/

/--
info: 'LeanerVM.Protocol.EndToEnd.Sound.retOK_busTable' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms retOK_busTable

/--
info: 'LeanerVM.Protocol.EndToEnd.Sound.retOK_publicInputPhase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms retOK_publicInputPhase

/-! ## What is load-bearing -/

/-- The predicate constrains the returns: `3` is not at most `2`. -/
example : ¬ RetOK (fun n : ℕ ↦ n ≤ 2) (Prog.ret 3) := by
  intro h
  have := h [] 3 rfl
  omega

/-- The bound is on the returns, not the reads: `readN 4` returns four scalars, not three. -/
example : ¬ RetOK (fun xs : List E ↦ xs.length ≤ 3) (Prog.readN 4) := by
  intro h
  have := h ([0, 0, 0, 0].map Ev.read) [0, 0, 0, 0] rfl
  simp at this

/-- A rejecting program returns nothing, so it satisfies even the false predicate. -/
example : RetOK (fun _ : ℕ ↦ False) Prog.fail := RetOK.fail

end LeanerVMTests.Protocol.EndToEnd.Sound.Returns
