/-
  LeanVM.Guest.Memory.RestrictB

  Restricting the loads of a call tree to its support (`Restrict.lean`) under any semantics
  of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.Restrict
public import LeanVM.Guest.Memory.RetempB

/-!
# Restricting loads under any `BLAKE2S` semantics

`Restrict.lean`'s lemmas with `S : BlakeSem` a parameter: `loadsB_of_supp`, `relInB_of_rel_supp`,
`eqnsB_read_pure`, `relAtInB_uniform_of_supp`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

section Supp

variable {P : Core.Program} {rd : Reader} {R : ℕ → Prop}

theorem loadsB_of_supp (hR : ∀ A v, rd A = some v → ∃ i, A = gpow i ∧ R i) {σ : Val} {es : List Ev}
    (hes : ∀ e ∈ es, e.HoldsB S rd σ) : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ R i := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  match e, he, hea with
  | .atom (.load d p off), he, hea =>
    simp only [Ev.loadAddr?, Option.some.injEq] at hea
    subst hea
    exact hR _ _ (hes _ he).2

mutual
/-- **A tree valid on a reader that reads nothing outside `R` loads from `R`.** -/
theorem loadsRB_of_supp (hR : ∀ A v, rd A = some v → ∃ i, A = gpow i ∧ R i) :
    ∀ (t : Tree) {args rets : List E}, t.ValidB S P rd args rets → t.LoadsR P R
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩ => by
      rw [Tree.LoadsR, events_node hf hw]
      exact ⟨loadsB_of_supp hR hes, loadsRKidsB_of_supp hR kids σ (calls es) hk⟩
  | .phantom .., _, _, h => h.elim

/-- `loadsRB_of_supp` for the callees. -/
theorem loadsRKidsB_of_supp (hR : ∀ A v, rd A = some v → ∃ i, A = gpow i ∧ R i) :
    ∀ (ks : List Tree) (σ : Val) (cs : List Call), Tree.KidsValidB S P rd σ cs ks → Tree.LoadsRKids P R ks
  | [], _, _, _ => by rw [Tree.LoadsRKids]; trivial
  | k :: ks, σ, c :: cs, ⟨_, hc, hks⟩ => by
      rw [Tree.LoadsRKids]
      refine ⟨?_, loadsRKidsB_of_supp hR ks σ cs hks⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact loadsRB_of_supp hR k hc
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        rw [Tree.LoadsR]; trivial
  | _ :: _, _, [], h => h.elim
end

/-- **A relation on a reader that reads nothing outside `R` loads from `R`.** -/
theorem relInB_of_rel_supp (hP : P.Wf) (hR : ∀ A v, rd A = some v → ∃ i, A = gpow i ∧ R i)
    {f : String} {args rets : List E} (h : P.RelB S rd f args rets) : P.RelInB S rd R f args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.RelB.tree hP h
  exact ⟨t, hn, hv, hb, loadsRB_of_supp hR t hv⟩

end Supp

/-! ## Pure functions -/

section Uniform

variable {P : Core.Program} {rd0 : Reader} {Sz : List String}

theorem atomEqnsB_read_pure {σ : Val} : ∀ (a : Atom), atomUnplaced a = true → a.HoldsB S rd0 σ →
    ∀ q ∈ atomEqns σ a, rd0 q.1 = some q.2
  | .load .., _, h, q, hq => by rw [List.mem_singleton.mp hq]; exact h.2
  | .rangeCheck .., _, h, q, hq => by
      simp only [atomEqns, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact h.1.2
      · exact h.2.2.2
  | .frameAddr .., hu, _, _, _ => by simp [atomUnplaced] at hu
  | .const .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .add .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .mul .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .copy .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .assertEq .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .assertNe .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .assertInK .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .blake2s .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .hint _, _, _, _, hq => (List.not_mem_nil hq).elim

mutual
/-- **A valid tree of a pure function reads what its memory holds**, every equation. -/
theorem eqnsB_read_pure (hS : P.PureIn Sz) : ∀ (t : Tree) {args rets : List E},
    t.ValidB S P rd0 args rets → t.name ∈ Sz → ∀ q ∈ t.eqns P, rd0 q.1 = some q.2
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩, hn, q, hq => by
      have hpure : ∀ e ∈ es, e.pure Sz := by
        have := walk_pure (σ := σ) fn.body (hS f hn fn hf)
        rwa [hw] at this
      rw [eqns_node hf hw] at hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨e, he, hqe⟩ := List.mem_flatMap.mp hq
        match e, he, hqe with
        | .atom a, he, hqe => exact atomEqnsB_read_pure a (hpure _ he) (hes _ he) q hqe
      · exact eqnsKidsB_read_pure hS kids σ (calls es) hk (calls_pure hpure) q hq
  | .phantom .., _, _, h, _, _, _ => h.elim

/-- `eqnsB_read_pure` for the callees. -/
theorem eqnsKidsB_read_pure (hS : P.PureIn Sz) : ∀ (ks : List Tree) (σ : Val) (cs : List Call),
    Tree.KidsValidB S P rd0 σ cs ks → (∀ c ∈ cs, c.f ∈ Sz) → ∀ q ∈ Tree.eqnsKids P ks, rd0 q.1 = some q.2
  | [], _, _, _, _, q, hq => by simp [Tree.eqnsKids] at hq
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hS', q, hq => by
      rw [Tree.eqnsKids] at hq
      rcases List.mem_append.mp hq with hq | hq
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact eqnsB_read_pure hS k hc (hn ▸ hS' c List.mem_cons_self) q hq
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          simp [Tree.eqns] at hq
      · exact eqnsKidsB_read_pure hS ks σ cs hks (fun c' h => hS' c' (List.mem_cons_of_mem _ h)) q hq
  | _ :: _, _, [], h, _, _, _ => h.elim
end

/-- **A pure function's relation on a reader reading nothing outside `R`, uniformly**: one size,
placed anywhere, on every memory extending that reader. -/
theorem relAtInB_uniform_of_supp (fs : String → ℕ) (cert : String → V → ℕ) (hP : P.Wf)
    (hS : P.PureIn Sz) {g : String} (hg : g ∈ Sz) {R : ℕ → Prop}
    (hR : ∀ A v, rd0 A = some v → ∃ i, A = gpow i ∧ R i) {args rets : List E}
    (h : P.RelB S rd0 g args rets) :
    ∃ n, ∀ fp (rd : Reader), (∀ A v, rd0 A = some v → rd A = some v) →
      RelAtInB S P fs cert rd R (fun _ => False) fp n g args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.RelB.tree hP h
  refine ⟨t.total fs, fun fp rd hext => ?_⟩
  have hv' := hv.transfer t fun q hq => hext _ _ (eqnsB_read_pure hS t hv (hn ▸ hg) q hq)
  exact ⟨t, hn, hv', hb, placedB_of_pure hS t hv hb (hn ▸ hg) fp, rfl,
    loadsIn_of_loadsR t R fp (loadsRB_of_supp hR t hv), fun _ h => h.elim⟩

end Uniform

end
end LeanVM.Guest.Memory
