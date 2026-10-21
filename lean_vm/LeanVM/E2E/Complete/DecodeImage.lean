/-
  LeanVM.E2E.Complete.DecodeImage

  The load equations of the honest tree's pre-retemp subtrees read back on the honest memory, and a
  valid tree's load equations hold on its reader.
-/

module

public import LeanVM.Guest.MemoryB
public import LeanVM.Guest.Memory.LoadEqns
public import LeanVM.Guest.Memory.GuestFresh

/-!
# Load equations on the honest memory

* `loadEqns_read_of_validB`: on the reader a tree is valid on, its load equations hold;
* `honest_read_loadEqns`: the honest memory of a retemped tree `T0.retemp …` reads back every load
  equation of `T0` (the retemped tree's are `T0`'s, `loadEqns_retemp`, and they are memory
  equations of the honest memory, `HonestB.read_eqn`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

section
variable {S : BlakeSem} {P : Core.Program} {rd : Reader}

theorem atomLoadEqns_read {σ : Val} : ∀ (a : Atom), a.HoldsB S rd σ →
    ∀ q ∈ atomLoadEqns σ a, rd q.1 = some q.2
  | .load d p off, h, q, hq => by
      simp only [atomLoadEqns, List.mem_singleton] at hq
      subst hq
      exact h.2
  | .const .., _, _, hq | .add .., _, _, hq | .mul .., _, _, hq | .copy .., _, _, hq
  | .assertEq .., _, _, hq | .assertNe .., _, _, hq | .rangeCheck .., _, _, hq
  | .assertInK .., _, _, hq | .blake2s .., _, _, hq | .frameAddr .., _, _, hq | .hint _, _, _, hq =>
      (List.not_mem_nil hq).elim

theorem evLoadEqns_read {σ : Val} {es : List Ev} (h : ∀ e ∈ es, e.HoldsB S rd σ) :
    ∀ q ∈ evLoadEqns σ es, rd q.1 = some q.2 := by
  intro q hq
  obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp hq
  cases e with
  | atom a => exact atomLoadEqns_read a (h _ he) q hq
  | _ => exact (List.not_mem_nil hq).elim

mutual
/-- **A valid tree's load equations hold on its reader.** -/
theorem loadEqns_read_of_validB : ∀ (t : Tree) {args rets : List E}, t.ValidB S P rd args rets →
    ∀ q ∈ t.loadEqns P, rd q.1 = some q.2
  | .node _ σ _ kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩, q, hq => by
      rw [Tree.loadEqns, events_node hf hw, List.mem_append] at hq
      rcases hq with hq | hq
      · exact evLoadEqns_read hes q hq
      · exact loadEqnsKids_read_of_validB σ kids _ hk q hq
  | .phantom .., _, _, h, _, _ => h.elim

/-- `loadEqns_read_of_validB` for the callees. -/
theorem loadEqnsKids_read_of_validB : ∀ (σ : Val) (ks : List Tree) (cs : List Call),
    Tree.KidsValidB S P rd σ cs ks → ∀ q ∈ Tree.loadEqnsKids P ks, rd q.1 = some q.2
  | _, [], _, _, _, hq => by rw [Tree.loadEqnsKids] at hq; exact (List.not_mem_nil hq).elim
  | _, _ :: _, [], h, _, _ => h.elim
  | σ, k :: ks, c :: cs, ⟨_, hc, hks⟩, q, hq => by
      rw [Tree.loadEqnsKids, List.mem_append] at hq
      rcases hq with hq | hq
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact loadEqns_read_of_validB k hc q hq
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          rw [Tree.loadEqns] at hq
          exact (List.not_mem_nil hq).elim
      · exact loadEqnsKids_read_of_validB σ ks cs hks q hq
end

end

/-- **The honest memory of a retemped tree reads back the original tree's load equations.** -/
theorem honest_read_loadEqns {S : BlakeSem} {fs : String → ℕ} {H : Inst → ℕ → E × E}
    {C : Inst → List (ℕ × E)} {hdr : E × E} {T0 : Tree} {ν : ℕ → String → Val → V → E}
    {rd : Reader} {args rets : List E}
    (hH : HonestB S coreProgram fs H C hdr (T0.retemp coreProgram fs ν 0) rd args rets) :
    ∀ q ∈ T0.loadEqns coreProgram,
      (honest coreProgram fs H C hdr (T0.retemp coreProgram fs ν 0)).read q.1 = some q.2 := by
  intro q hq
  rw [← loadEqns_retemp coreProgram_fresh T0 0 (fs := fs) (ν := ν)] at hq
  exact hH.read_eqn (mem_eqns_of_mem_loadEqns _ hq)

end
end LeanVM.E2E.Complete
