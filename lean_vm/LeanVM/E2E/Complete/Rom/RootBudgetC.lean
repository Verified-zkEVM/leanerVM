/-
  LeanVM.E2E.Complete.Rom.RootBudgetC

  T6-prob's two-level inhabitant: the deployed budget's words but `open_stacked`'s bound, at the
  work of a node with one child, by kernel evaluation one coefficient at a time.
-/

module

public import LeanVM.E2E.Complete.Rom.RootBudgetB

/-!
# The budget at a node with one child, but `open_stacked`'s bound

`rootWork = ⟨1, 1, 0, 0, 0, 0, 1, 1⟩`: one declared claim, one coverage slot, one child making one
claim. A linear bound at it is the sum of five of its coefficients (`Linear.eval_rootWork`): the
other four are weighted by `0`, and the kernel would still evaluate them in a whole `eval`. So each
of the five is evaluated alone, and the sum is taken symbolically.

At it: the words, `open_stacked`'s bound `Bop` set to `0` (`rootBdRest`), are within `2^20`
(`rootWords_rest_le`). The instructions are `RootBudgetD.lean`'s to `RootBudgetF.lean`'s;
`RootBudget.lean` adds `Bop`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B2C

@[expose] public section

/-- The work of a node with one child and one claim held through it. -/
def rootWork : End.Work := ⟨1, 1, 0, 0, 0, 0, 1, 1⟩

/-- **A linear bound at the root's work**: its constant plus its four coefficients weighted by
`1`. -/
theorem Linear.eval_rootWork (l : End.Linear) :
    l.eval rootWork = l.base + l.declared + l.coverage + l.children + l.childClaims := by
  simp only [End.Linear.eval, rootWork, Nat.mul_one, Nat.mul_zero, Nat.add_zero]

/-! ## The words -/

/-- `main`'s callees' bounds, `open_stacked`'s set to `0` in `verify_sub`'s. -/
noncomputable def rootBdRest : Main.CalleeBounds :=
  { Main.calleeBd fs calleesHyps_b2c with
    vs := VerifySub.vsBound fs { Main.calleeVsB fs calleesHyps_b2c with op := 0 } }

theorem rootWordsRest_base :
    (Main.eaLin fs rootBdRest (Main.eaWordsC fs calleesHyps_b2c 482 0)).base ≤ 2 ^ 14 := by
  decide +kernel

theorem rootWordsRest_declared :
    (Main.eaLin fs rootBdRest (Main.eaWordsC fs calleesHyps_b2c 482 0)).declared ≤ 2 ^ 12 := by
  decide +kernel

theorem rootWordsRest_coverage :
    (Main.eaLin fs rootBdRest (Main.eaWordsC fs calleesHyps_b2c 482 0)).coverage ≤ 2 ^ 12 := by
  decide +kernel

theorem rootWordsRest_children :
    (Main.eaLin fs rootBdRest (Main.eaWordsC fs calleesHyps_b2c 482 0)).children ≤ 2 ^ 19 := by
  decide +kernel

theorem rootWordsRest_childClaims :
    (Main.eaLin fs rootBdRest (Main.eaWordsC fs calleesHyps_b2c 482 0)).childClaims ≤ 2 ^ 12 := by
  decide +kernel

/-- The rest of the words at the root's work, `Bop` set to `0`. -/
theorem rootWords_rest_le :
    (Main.eaLin fs rootBdRest (Main.eaWordsC fs calleesHyps_b2c 482 0)).eval rootWork ≤ 2 ^ 20 := by
  rw [Linear.eval_rootWork]
  have := rootWordsRest_base
  have := rootWordsRest_declared
  have := rootWordsRest_coverage
  have := rootWordsRest_children
  have := rootWordsRest_childClaims
  omega

end
end LeanVM.E2E.Complete
