/-
  LeanVM.Guest.B1.Comp.Whir.LocT.Loads

  The callee tree at a call of a linked node.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.Decode
public import LeanVM.Guest.B1.Comp.TreeRoot
public import LeanVM.Guest.B1.Comp.Tables.LoadsL

/-!
# Load equations of trees

(The load equations of a node's path and callees: `Comp/Tables/LoadsL.lean`.) `kids_call`: under `KidsSat` and
`KidsLinkCalls` a call of the path has its callee tree, satisfying the call's predicate, with the
callee's valuation under `V`, valid on the call's words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

variable {P : Core.Program} {σ : Val}

/-- `KidsLink` of a member callee. -/
theorem kidsLinkKids_mem {V : FrameVals} : ∀ {ks : List Tree} {k : Tree}, k ∈ ks → KidsLinkKids V ks →
    KidsLink V k
  | [], _, h, _ => absurd h List.not_mem_nil
  | _ :: ks, _, h, hl => by
    rw [KidsLinkKids] at hl
    rcases List.mem_cons.mp h with rfl | h
    · exact hl.1
    · exact kidsLinkKids_mem h hl.2

/-- **The callee tree of an entered call**, from the path's callees: it satisfies the call's
predicate where it is placed, it is valid on the call's words, and under a linked `V` the call's
valuation is the callee's. -/
theorem kids_call {S : BlakeSem} {rd : Reader} {V : FrameVals} {qf : Call → ℕ → Tree → Prop} :
    ∀ {cs : List Call} {bs : List ℕ} {ks : List Tree}, Tree.KidsValidB S P rd σ cs ks →
      KidsSat cs (cs.map qf) bs ks → KidsLinkCalls V σ cs ks → bs.length = ks.length →
      ∀ c ∈ cs, c.taken = true → ∃ k ∈ ks, ∃ b, qf c b k ∧ k.ValidB S P rd (c.args.map σ) (c.rets.map σ) ∧
        k.name = c.f ∧ (c.f ∈ osDecNames → B2C.NodeAgree k (V c.f (c.args.map σ) (c.rets.map σ)))
  | [], _, _, _, _, _, _, c, hc, _ => absurd hc List.not_mem_nil
  | _ :: _, _, [], hv, _, _, _, _, _, _ => by simp [Tree.KidsValidB] at hv
  | c1 :: cs, [], k :: ks, _, _, _, hbl, _, _, _ => absurd hbl (by simp)
  | c1 :: cs, b :: bs, k :: ks, hv, hs, hl, hbl, c, hc, ht => by
    simp only [List.map_cons, KidsSat] at hs
    simp only [Tree.KidsValidB] at hv
    rw [KidsLinkCalls] at hl
    rcases List.mem_cons.mp hc with rfl | hc
    · have hv1 := hv.2.1
      rw [ite_eq_left ht] at hv1
      exact ⟨k, List.mem_cons_self, b, hs.1 ht, hv1, hv.1, hl.1 ht⟩
    · obtain ⟨k', hk', b', h1, h2, h3, h4⟩ := kids_call hv.2.2 hs.2 hl.2 (by simpa using hbl) c hc ht
      exact ⟨k', List.mem_cons_of_mem _ hk', b', h1, h2, h3, h4⟩

end
end LeanVM.Guest.B1
