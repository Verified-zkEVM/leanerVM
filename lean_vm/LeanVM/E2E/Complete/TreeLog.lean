/-
  LeanVM.E2E.Complete.TreeLog

  T6-det with L17 reduced to a count: the honest tree within the limits, every node's log of
  hashed strings (`nodeLog`) having fewer than `2^64` block prefixes, in place of `NodeSupport`.
-/

module

public import LeanVM.E2E.Complete.Tree
public import LeanVM.E2E.Complete.NodeLog

/-!
# T6-det, L17 a count

`HonestTree.WithinLimits` (`Tree.lean`) keeps L17 as `NodeSupport` at every node: a list of
strings supporting the node's digest and relation, with fewer than `2^64` block prefixes. The list
is now built (`nodeLog`, `NodeLog.lean`) and supports them (`nodeSupport_of_count`), so the
hypothesis left is the count alone: `HonestTree.WithinLimits'` asks, at every node, the deployed
limits, the budget, and `(prefixesOf (nodeLog H s w)).length < 2 ^ 64`. It gives
`WithinLimits` (`HonestTree.withinLimits_of'`), and `idealVerify_complete''` is
`idealVerify_complete'` under it.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest LeanVM.Protocol.LeanIsa

@[expose] public section

/-- A condition implied at every node is implied of the tree. -/
theorem HonestTree.allNodes_imp {P Q : HonestTree → Prop} (h : ∀ T, P T → Q T) :
    ∀ T : HonestTree, T.AllNodes P → T.AllNodes Q := by
  refine HonestTree.induct' _ fun c xs ss ds kids ih hP ↦ ?_
  rw [HonestTree.allNodes_node] at hP ⊢
  exact ⟨h _ hP.1, fun k hk ↦ ih k hk (hP.2 k hk)⟩

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-- **The node within the limits, L17 a count**: at the deferred claim the honest prover finds
from its children's outputs, the deployed limits, the budget, and fewer than `2^64` block
prefixes of the strings the node's checks hash. -/
def HonestTree.LimitsAt' : HonestTree → Prop
  | .node claims xs ss ds kids =>
    ∀ kos, kidOuts H ρ pfuel kids = some kos → ∀ hd, honestDefer H (kos.map HonestOut.child) = some hd →
      End.Limits ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩ ∧
      B2C.b2cBudget'.size (End.work ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩) ≤
        2 ^ 28 ∧
      (prefixesOf (nodeLog H ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩)).length <
        2 ^ 64

/-- **The tree within the limits, L17 a count**, at every node. -/
def HonestTree.WithinLimits' (T : HonestTree) : Prop :=
  T.AllNodes (HonestTree.LimitsAt' H ρ pfuel)

/-- The count gives `NodeSupport`, so `WithinLimits'` gives `WithinLimits`. -/
theorem HonestTree.withinLimits_of' {T : HonestTree} (h : T.WithinLimits' H ρ pfuel) :
    T.WithinLimits H ρ pfuel := by
  refine HonestTree.allNodes_imp (fun T' hT' ↦ ?_) T h
  obtain ⟨c, xs, ss, ds, kids⟩ := T'
  intro kos hkos hd hdef
  obtain ⟨hlim, hbud, hcount⟩ := hT' kos hkos hd hdef
  exact ⟨hlim, hbud, nodeSupport_of_count hcount⟩

/-- **T6-det, L17 a count**: `idealVerify_complete'` with the tree within the limits as
`WithinLimits'`, every node's log of hashed strings having fewer than `2^64` block prefixes. -/
theorem idealVerify_complete'' (hL2 : GuestCompleteModel) (T : HonestTree) {fuel : ℕ}
    (hρ : validRate ρ) (hv : T.Valid H) (hlim : T.WithinLimits' H ρ pfuel)
    (hpow : T.PowFound H ρ pfuel) (hw : T.WeightsNonzero H ρ pfuel)
    (hroots : T.RootsInjAt H ρ pfuel) (hfuel : T.size ≤ fuel) :
    ∃ s ip, honestIdeal H ρ pfuel T = some (s, ip) ∧ s.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest ip fuel s = true :=
  idealVerify_complete' H ρ pfuel hL2 T hρ hv (HonestTree.withinLimits_of' H ρ pfuel hlim) hpow hw
    hroots hfuel

end
end LeanVM.E2E.Complete
