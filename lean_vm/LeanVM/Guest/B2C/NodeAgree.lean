/-
  LeanVM.Guest.B2C.NodeAgree

  A valuation agreeing with a call tree's node on the cells its path names: what a decoder's
  valuation at an honest frame gives of the instance's valuation.
-/

module

public import LeanVM.Guest.B2C.Cells

/-!
# Agreeing with a node on its named cells

A decoder reads a callee's valuation at a frame of the memory (`Located.valAt`). At an honest
frame it is the instance's valuation on every value the instance's path names whose cell lies in
the frame (`namedOf`, `cellJ`, `fsN`), and only there: elsewhere the frame's cells are whatever
the memory holds, while the tree's valuation is arbitrary. `NodeAgree t σ'` states exactly that
agreement, the form the decoders' congruence lemmas take as hypothesis.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **`σ'` agrees with the node `t` on its named cells**: on every value `t`'s path names whose
cell lies in `t`'s frame, `σ'` is `t`'s valuation. -/
def NodeAgree (t : Tree) (σ' : Val) : Prop :=
  ∀ j, idxOf t.name = some j → ∀ es vs, walk t.val (coreOf j).body = .ret es vs →
    ∀ v ∈ namedOf (coreOf j).params es vs, 2 ≤ cellJ j v → cellJ j v < fsN j → σ' v = t.val v

/-- `NodeAgree` at a node, value by value. -/
theorem NodeAgree.eq {f : String} {σ σ' : Val} {bufs : List ℕ} {ks : List Tree}
    (h : NodeAgree (.node f σ bufs ks) σ') {j : ℕ} (hj : idxOf f = some j) {es : List Ev}
    {vs : List V} (hw : walk σ (coreOf j).body = .ret es vs) {v : V}
    (hv : v ∈ namedOf (coreOf j).params es vs) (h2 : 2 ≤ cellJ j v) (hn : cellJ j v < fsN j) :
    σ' v = σ v :=
  h j hj es vs hw v hv h2 hn

/-- The node agrees with itself. -/
theorem nodeAgree_refl (t : Tree) : NodeAgree t t.val := fun _ _ _ _ _ _ _ _ _ => rfl

end
end LeanVM.Guest.B2C
