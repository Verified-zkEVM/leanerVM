/-
  LeanVM.E2E.Complete.Rom.Kids

  A node of an honest tree has at most 16 children.
-/

module

public import LeanVM.E2E.Complete.Prover

namespace LeanVM.E2E.Complete

@[expose] public section

/-- **At most 16 children** at the tree's root node (the guest's limit on children). -/
def HonestTree.KidsLe16 : HonestTree → Prop
  | .node _ _ _ _ kids => kids.length ≤ 16

end
end LeanVM.E2E.Complete
