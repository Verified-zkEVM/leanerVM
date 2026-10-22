/-
  LeanVM.E2E.Complete.Count.Final

  T6-det under the deployed limits and budget alone: L17's count is derived at every node of a
  valid honest tree.
-/

module

public import LeanVM.E2E.Complete.Count.Node
public import LeanVM.E2E.Complete.DecodeFinal

/-!
# T6-det, the count derived

`HonestTree.WithinLimits'` (`TreeLog.lean`) asks at every node the deployed limits, the budget
and L17's count. The count is now a theorem (`nodeLog_count_lt`, `Count/Node.lean`) from the
limits and the node relation, and at every node of a valid honest tree the node relation holds at
`some ∘ H` (`nodeRel_honest`, L12, from the node's holders and its children's outputs). So:

* `HonestTree.LimitsBudgetAt` / `HonestTree.WithinLimitsBudget`: the deployed limits and the
  budget at every node, without the count;
* `HonestTree.withinLimits'_of_budget`: with the holders valid at every node and a valid rate, they
  give `WithinLimits'`;
* **`idealVerify_complete_final`**: T6-det (`idealVerify_complete_det`) under
  `WithinLimitsBudget`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest LeanVM.Protocol.LeanIsa

@[expose] public section

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-- **The node within the deployed limits and the budget**, at the deferred claim the honest
prover finds from its children's outputs. -/
def HonestTree.LimitsBudgetAt : HonestTree → Prop
  | .node claims xs ss ds kids =>
    ∀ kos, kidOuts H ρ pfuel kids = some kos → ∀ hd, honestDefer H (kos.map HonestOut.child) = some hd →
      End.Limits ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩ ∧
      B2C.b2cBudget'.size (End.work ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩) ≤
        2 ^ 28

/-- **The tree within the deployed limits and the budget**, at every node. -/
def HonestTree.WithinLimitsBudget (T : HonestTree) : Prop :=
  T.AllNodes (HonestTree.LimitsBudgetAt H ρ pfuel)

/-- Two conditions at every node hold together at every node. -/
theorem HonestTree.allNodes_and {P Q : HonestTree → Prop} :
    ∀ T : HonestTree, T.AllNodes P → T.AllNodes Q → T.AllNodes (fun T ↦ P T ∧ Q T) := by
  refine HonestTree.induct' _ fun c xs ss ds kids ih hP hQ ↦ ?_
  rw [HonestTree.allNodes_node] at hP hQ ⊢
  exact ⟨⟨hP.1, hQ.1⟩, fun k hk ↦ ih k hk (hP.2 k hk) (hQ.2 k hk)⟩

/-- **The count at a node**: with its holders valid and a valid rate, the deployed limits and the
budget give L17's count, through the honest node relation. -/
theorem HonestTree.limitsAt'_of_budget (hρ : validRate ρ) :
    ∀ T : HonestTree, HonestTree.ValidAt H T → HonestTree.LimitsBudgetAt H ρ pfuel T →
      HonestTree.LimitsAt' H ρ pfuel T
  | .node claims xs ss ds kids, hv, hl => by
    intro kos hkos hd hdef
    obtain ⟨hlim, hbud⟩ := hl kos hkos hd hdef
    refine ⟨hlim, hbud, nodeLog_count_lt hlim ?_⟩
    have h2 := forall₂_kidOuts H ρ pfuel hkos
    have hchild : ∀ ko ∈ kos, _ := fun ko hko ↦
      (forall₂_mem_right h2 ko hko).elim fun k hk ↦ honestOut_child H ρ pfuel hρ hk.2
    have hc := (kidOuts_claims H ρ pfuel hkos).symm
    obtain ⟨hx, hs, hda⟩ := hv
    exact nodeRel_honest H hdef (fun ko hko ↦ ⟨(hchild ko hko).1, (hchild ko hko).2.2.1⟩)
      (hx.imp fun _ _ h ↦ xmssHeldWith_transfer hc h)
      (hs.imp fun _ _ h ↦ sphincsHeldWith_transfer hc h)
      (hda.imp fun _ _ h ↦ daHeldWith_transfer hc h)

/-- **The count derived**: a tree whose holders are valid at every node, within the deployed
limits and the budget, at a valid rate, is within `WithinLimits'`. -/
theorem HonestTree.withinLimits'_of_budget (hρ : validRate ρ) {T : HonestTree}
    (hv : T.AllNodes (HonestTree.ValidAt H)) (h : T.WithinLimitsBudget H ρ pfuel) :
    T.WithinLimits' H ρ pfuel :=
  HonestTree.allNodes_imp (fun T' hT' ↦ HonestTree.limitsAt'_of_budget H ρ pfuel hρ T' hT'.1 hT'.2)
    T (HonestTree.allNodes_and T hv h)

/-- `WithinLimits'` gives the deployed limits and the budget. -/
theorem HonestTree.withinLimitsBudget_of' {T : HonestTree} (h : T.WithinLimits' H ρ pfuel) :
    T.WithinLimitsBudget H ρ pfuel := by
  refine HonestTree.allNodes_imp (fun T' hT' ↦ ?_) T h
  obtain ⟨c, xs, ss, ds, kids⟩ := T'
  intro kos hkos hd hdef
  obtain ⟨hlim, hbud, -⟩ := hT' kos hkos hd hdef
  exact ⟨hlim, hbud⟩

/-- **T6-det under the deployed limits**: for every hash `H`, a valid honest witness tree within
the deployed limits and the budget at every node, at a valid rate and a fuel at least the tree's
size, under the good events G1 (`PowFound`), G2 (`WeightsNonzero`) and G3 (`RootsInjAt`): the
honest idealized prover outputs a statement with the tree's claims and an idealized proof that
V_I accepts. No hypothesis on the guest (L2 is `guestCompleteModel`) nor on the node's hashed
strings (L17 is `nodeLog_count_lt`). -/
theorem idealVerify_complete_final (T : HonestTree) {fuel : ℕ}
    (hρ : validRate ρ) (hv : T.Valid H) (hlim : T.WithinLimitsBudget H ρ pfuel)
    (hpow : T.PowFound H ρ pfuel) (hw : T.WeightsNonzero H ρ pfuel)
    (hroots : T.RootsInjAt H ρ pfuel) (hfuel : T.size ≤ fuel) :
    ∃ s ip, honestIdeal H ρ pfuel T = some (s, ip) ∧ s.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest ip fuel s = true :=
  idealVerify_complete_det H ρ pfuel T hρ hv
    (HonestTree.withinLimits'_of_budget H ρ pfuel hρ hv.1 hlim) hpow hw hroots hfuel

end
end LeanVM.E2E.Complete
