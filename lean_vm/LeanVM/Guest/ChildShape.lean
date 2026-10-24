/-
  LeanVM.Guest.ChildShape

  A child's announced stack log and rate: which of the guest's opening arms its `verify_sub`
  dispatches to, the parameter a child's share of the budget depends on.
-/

module

public import LeanVM.Spec.Node
public import LeanVM.Protocol.Verifier

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **A child's announced stack log and rate** (`readSizes`, `Verifier.announced`): the opening
arm its `verify_sub` dispatches to (G:3314-3316); `(0, 0)` if its stream announces none, which no
child of a node within `Limits`, its caps agreeing and no zero challenge, does
(`B1.Main.childShape_bounds`). -/
def childShape (bytecode : List K) (c : Child) : ℕ × ℕ :=
  match announced bytecode c.proof.stream with
  | some (layout, r) => (layout.stackLog, r)
  | none => (0, 0)

theorem childShape_of {bytecode : List K} {c : Child} {layout : Layout} {r : ℕ}
    (h : announced bytecode c.proof.stream = some (layout, r)) :
    childShape bytecode c = (layout.stackLog, r) := by
  unfold childShape; rw [h]

end
end LeanVM.Guest
