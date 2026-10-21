/-
  LeanVM.Guest.B1.Comp.Whir.LocT.Agree

  A valid tree's memory satisfies its load equations; a reader satisfying them reads what the
  tree's memory holds at every address loaded.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.Loads
public import LeanVM.Guest.B1.Whir.Cap

/-!
# Readers agreeing on a tree's loads

`validB_loadEqns`: the memory a tree is valid on satisfies its load equations. Hence any other
reader satisfying them reads the same words at every address the tree loads (`memAt_agree`): a
decoder reading only loaded addresses reads the honest memory's words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem} {P : Core.Program} {rd : Reader}

theorem evLoadEqns_read {σ : Val} {es : List Ev} (hes : ∀ e ∈ es, e.HoldsB S rd σ) :
    ∀ q ∈ evLoadEqns σ es, rd q.1 = some q.2 := by
  intro q hq
  obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp hq
  match e, hq, hes e he with
  | .atom (.load d p off), hq, h => rw [List.mem_singleton.mp hq]; exact h.2

mutual
/-- **A valid tree's memory satisfies its load equations.** -/
theorem validB_loadEqns : ∀ (t : Tree) {args rets : List E}, t.ValidB S P rd args rets →
    ∀ q ∈ t.loadEqns P, rd q.1 = some q.2
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩ => by
      intro q hq
      rw [Tree.loadEqns, events_node hf hw, List.mem_append] at hq
      rcases hq with hq | hq
      · exact evLoadEqns_read hes q hq
      · exact kidsValidB_loadEqns _ _ hk q hq
  | .phantom .., _, _, h => h.elim

/-- `validB_loadEqns` of the callees. -/
theorem kidsValidB_loadEqns {σ : Val} : ∀ (cs : List Call) (ks : List Tree),
    Tree.KidsValidB S P rd σ cs ks → ∀ q ∈ Tree.loadEqnsKids P ks, rd q.1 = some q.2
  | [], [], _, q, hq => by rw [Tree.loadEqnsKids] at hq; exact absurd hq List.not_mem_nil
  | c :: cs, k :: ks, ⟨_, hv, hks⟩, q, hq => by
      rw [Tree.loadEqnsKids, List.mem_append] at hq
      rcases hq with hq | hq
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hv
          exact validB_loadEqns k hv q hq
        · rw [ite_eq_right ht] at hv
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hv
          rw [Tree.loadEqns] at hq
          exact absurd hq List.not_mem_nil
      · exact kidsValidB_loadEqns cs ks hks q hq
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
end

/-- Readers satisfying a list of memory equations. -/
def Sat (rd : Reader) (L : List (K × E)) : Prop := ∀ q ∈ L, rd q.1 = some q.2

/-- **Two readers satisfying the same equations read alike at an address they name.** -/
theorem memAt_agree {L : List (K × E)} {rd' : Reader} (h : Sat rd L) (h' : Sat rd' L) {p : E} {off : ℕ}
    {v : E} (hm : (p.limb 0 * Parameters.gpow off, v) ∈ L) : memAt rd' p off = memAt rd p off := by
  simp only [memAt, h _ hm, h' _ hm]

theorem Sat.mono {L L' : List (K × E)} {rd' : Reader} (h : Sat rd' L') (hs : ∀ q ∈ L, q ∈ L') : Sat rd' L :=
  fun q hq => h q (hs q hq)

/-- A load atom of a node's path names its address among the node's load equations. -/
theorem mem_loadEqns_load {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn} {es : List Ev}
    {vs : List V} (hf : P.find? f = some fn) (hw : walk σ fn.body = .ret es vs) {d p : V} {off : ℕ}
    (h : Ev.atom (.load d p off) ∈ es) :
    ((σ p).limb 0 * Parameters.gpow off, σ d) ∈ (Memory.Tree.node f σ bufs kids).loadEqns P :=
  mem_loadEqns_node hf hw (mem_evLoadEqns h)

end
end LeanVM.Guest.B1
