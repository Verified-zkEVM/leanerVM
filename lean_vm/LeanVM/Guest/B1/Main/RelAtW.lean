/-
  LeanVM.Guest.B1.Main.RelAtW

  `RelAtIn` with the root's valuation exposed: the tree a composition builds is the function's
  node at the valuation its walk ran on.
-/

module

public import LeanVM.Guest.Memory.Regions

/-!
# The placed relation, its root's valuation exposed

`RelAtInW … Q`: `RelAtIn` by a tree `.node f σ bufs kids` with `Q σ`. `relAtInW_of_walk` is
`relAtIn_of_walk` (`Memory/Regions.lean`, same proof) with the root's valuation the walk's;
`RelAtInW.relAtIn` forgets it.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ)

/-- **`RelAtIn` by a tree rooted at a valuation satisfying `Q`.** -/
def RelAtInW (rd : Reader) (R D : ℕ → Prop) (fp n : ℕ) (f : String) (args rets : List E)
    (Q : Val → Prop) : Prop :=
  ∃ t : Tree, (t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P ∧ t.Placed P fs cert fp ∧
    t.total fs = n ∧ t.LoadsIn P fs cert R fp ∧ ∀ i, D i → t.Data P fs cert fp i) ∧
    ∃ σ bufs kids, t = .node f σ bufs kids ∧ Q σ

variable {P fs cert}

theorem RelAtInW.relAtIn {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Q : Val → Prop} (h : RelAtInW P fs cert rd R D fp n f args rets Q) :
    RelAtIn P fs cert rd R D fp n f args rets :=
  let ⟨t, ht, _⟩ := h
  ⟨t, ht⟩

theorem RelAtInW.mono {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Q Q' : Val → Prop} (h : RelAtInW P fs cert rd R D fp n f args rets Q) (hq : ∀ σ, Q σ → Q' σ) :
    RelAtInW P fs cert rd R D fp n f args rets Q' :=
  let ⟨t, ht, σ, b, k, he, hQ⟩ := h
  ⟨t, ht, σ, b, k, he, hq σ hQ⟩

variable {rd : Reader} {σ : Val}

/-- **Composition with regions, the root's valuation exposed**: `relAtIn_of_walk`, by the node at
the walk's valuation. -/
theorem relAtInW_of_walk (hP : P.Wf) {R D Dk : ℕ → Prop} {fp N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} (hf : P.find? f = some fn)
    (hl : P.loop f = false ∨ calls es = []) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromIn P fs cert rd σ (fun i => R i ∨ ownData cert fp (fp + fs f) f (allocs σ es) es i)
      (fun _ => False) (calls es) (fp + fs f + (allocs σ es).sum) N Dk)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ R i ∨ Dk i))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ Dk i) :
    RelAtInW P fs cert rd R D fp (fs f + (allocs σ es).sum + N) f args rets (· = σ) := by
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl⟩ :=
    kids_of_kidsFromIn _ _ _ _ _ _ (takes_of_calls hP (List.mem_of_find?_eq_some hf) hw) hk
  have hl' : P.loop f = false ∨ ks.map (Tree.total fs) = [] := by
    rcases hl with hl | hl
    · exact Or.inl hl
    · rw [hl] at hkv
      cases ks with
      | nil => exact Or.inr rfl
      | cons _ _ => exact hkv.elim
  obtain ⟨hbb, hkpos⟩ := kidPos_not_loop (fs := fs) (fp := fp) (bufs := allocs σ es) hl'
  have hdata : ∀ i, (Tree.node f σ (allocs σ es) ks).Data P fs cert fp i ↔
      ownData cert fp (fp + fs f) f (allocs σ es) es i ∨
        Tree.DataKids P fs cert (bases (fp + fs f + (allocs σ es).sum) (ks.map (Tree.total fs))) ks i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos]
  refine ⟨.node f σ (allocs σ es) ks, ⟨rfl, ⟨fn, hf, hp, es, vs, hw, hr, hes, hkv⟩, ?_, ?_, ?_, ?_, ?_⟩,
    σ, _, _, rfl, rfl⟩
  · rw [Tree.BufsOk, events_node hf hw]
    exact ⟨rfl, hkb⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    exact ⟨⟨hbuf, haddr⟩, hkp⟩
  · rw [total_node, totalKids_eq_sum, hks]
    omega
  · rw [loadsIn_node, events_node hf hw, hkpos]
    refine ⟨fun A hA => ?_, hkl _ (fun i hi => ?_) (fun _ h => h.elim) (fun i hi => ?_)⟩
    · obtain ⟨i, hi, h⟩ := hload A hA
      refine ⟨i, hi, ?_⟩
      rw [hdata]
      rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact (hkd i h).elim (fun h => h.elim) fun h => Or.inl (Or.inr h)
    · rcases hi with h | h
      · exact Or.inr h
      · exact Or.inl ((hdata i).mpr (Or.inl h))
    · exact Or.inl ((hdata i).mpr (Or.inr hi))
  · intro i hi
    rw [hdata]
    rcases hD i hi with h | h
    · exact Or.inl h
    · exact (hkd i h).elim (fun h => h.elim) fun h => Or.inr h

end
end LeanVM.Guest.Memory
