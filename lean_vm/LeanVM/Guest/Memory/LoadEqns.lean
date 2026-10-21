/-
  LeanVM.Guest.Memory.LoadEqns

  The load equations of an evaluation: the memory words its paths' loads read. They are among its
  memory equations and survive re-choosing the temporaries.
-/

module

public import LeanVM.Guest.Memory.Retemp

/-!
# Load equations

`Tree.eqns` collects every memory equation of an evaluation's paths: loads, range checks and frame
runs (`atomEqns`). Re-choosing the range checks' temporaries (`Tree.retemp`, used to build the
honest memory) changes the range checks' equations, but not the loads': a load's value and
pointer are named in the body, which no temporary is (`Fn.Fresh`). `Tree.loadEqns` keeps the loads'
equations only:

* `atomLoadEqns`, `evLoadEqns`, `Tree.loadEqns`, `Tree.loadEqnsKids`;
* `mem_eqns_of_mem_loadEqns`: they are memory equations (`loadEqns ⊆ eqns`);
* `loadEqns_retemp`: on a program with fresh temporaries the re-chosen tree has the same load
  equations.

A fact a decoder needs of a memory, stated for every reader satisfying a tree's load equations,
thus holds of the honest memory of its re-chosen tree.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- A load's memory equation: the word at `p·g^off` is `d`. -/
def atomLoadEqns (σ : Val) : Atom → List (K × E)
  | .load d p off => [((σ p).limb 0 * gpow off, σ d)]
  | _ => []

/-- The load equations of events. -/
def evLoadEqns (σ : Val) (es : List Ev) : List (K × E) :=
  es.flatMap fun
    | .atom a => atomLoadEqns σ a
    | _ => []

mutual
/-- **The load equations of an evaluation**: those of every path of every call instance run. -/
noncomputable def Tree.loadEqns (P : Core.Program) : Tree → List (K × E)
  | t@(.node _ σ _ kids) => evLoadEqns σ (t.events P) ++ Tree.loadEqnsKids P kids
  | .phantom .. => []

/-- `Tree.loadEqns` of the callees. -/
noncomputable def Tree.loadEqnsKids (P : Core.Program) : List Tree → List (K × E)
  | [] => []
  | k :: ks => k.loadEqns P ++ Tree.loadEqnsKids P ks
end

variable {P : Core.Program}

theorem mem_atomEqns_of_mem_atomLoadEqns {σ : Val} {q : K × E} :
    ∀ {a : Atom}, q ∈ atomLoadEqns σ a → q ∈ atomEqns σ a
  | .load .., h => h
  | .const .., h | .add .., h | .mul .., h | .copy .., h | .assertEq .., h | .assertNe .., h
  | .rangeCheck .., h | .assertInK .., h | .blake2s .., h | .frameAddr .., h | .hint _, h =>
      (List.not_mem_nil h).elim

theorem mem_evEqns_of_mem_evLoadEqns {σ : Val} {q : K × E} {es : List Ev}
    (h : q ∈ evLoadEqns σ es) : q ∈ evEqns σ es := by
  obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp h
  refine List.mem_flatMap.mpr ⟨e, he, ?_⟩
  cases e with
  | atom a => exact mem_atomEqns_of_mem_atomLoadEqns hq
  | _ => exact (List.not_mem_nil hq).elim

mutual
/-- **The load equations are memory equations.** -/
theorem mem_eqns_of_mem_loadEqns : ∀ (t : Tree) {q : K × E}, q ∈ t.loadEqns P → q ∈ t.eqns P
  | .node f σ bufs kids, q, h => by
      rw [Tree.loadEqns, List.mem_append] at h
      rw [Tree.eqns, List.mem_append]
      rcases h with h | h
      · exact Or.inl (mem_evEqns_of_mem_evLoadEqns h)
      · exact Or.inr (mem_eqnsKids_of_mem_loadEqnsKids kids h)
  | .phantom .., _, h => by rw [Tree.loadEqns] at h; exact (List.not_mem_nil h).elim

/-- `mem_eqns_of_mem_loadEqns` for the callees. -/
theorem mem_eqnsKids_of_mem_loadEqnsKids : ∀ (ks : List Tree) {q : K × E},
    q ∈ Tree.loadEqnsKids P ks → q ∈ Tree.eqnsKids P ks
  | [], _, h => by rw [Tree.loadEqnsKids] at h; exact (List.not_mem_nil h).elim
  | k :: ks, q, h => by
      rw [Tree.loadEqnsKids, List.mem_append] at h
      rw [Tree.eqnsKids, List.mem_append]
      rcases h with h | h
      · exact Or.inl (mem_eqns_of_mem_loadEqns k h)
      · exact Or.inr (mem_eqnsKids_of_mem_loadEqnsKids ks h)
end

/-- A reader satisfying a tree's memory equations satisfies its load equations. -/
theorem loadEqns_of_eqns {rd : Reader} {t : Tree} (h : ∀ q ∈ t.eqns P, rd q.1 = some q.2) :
    ∀ q ∈ t.loadEqns P, rd q.1 = some q.2 :=
  fun q hq => h q (mem_eqns_of_mem_loadEqns t hq)

/-- Load equations of events whose values agree. -/
theorem evLoadEqns_congr {σ σ' : Val} {es : List Ev} (h : ∀ e ∈ es, ∀ v ∈ e.uses, σ' v = σ v) :
    evLoadEqns σ' es = evLoadEqns σ es := by
  unfold evLoadEqns
  refine List.flatMap_congr fun e he => ?_
  cases e with
  | atom a =>
      cases a with
      | load d p off =>
          have hd := h _ he d (by simp [Ev.uses, atomUses])
          have hp := h _ he p (by simp [Ev.uses, atomUses])
          simp only [atomLoadEqns, hd, hp]
      | _ => rfl
  | _ => rfl

section Retemp

variable {fs : String → ℕ} {ν : ℕ → String → Val → V → E}

/-- The re-chosen valuation gives a node's path the same load equations. -/
theorem evLoadEqns_retemp (hF : P.Fresh) {f : String} {fp : ℕ} {σ : Val} {bufs : List ℕ}
    {ks : List Tree} :
    evLoadEqns (retempVal P ν fp f σ) ((Tree.node f σ bufs ks).events P) =
      evLoadEqns σ ((Tree.node f σ bufs ks).events P) := by
  refine evLoadEqns_congr fun e he v hv => ?_
  unfold Tree.events at he
  simp only [Tree.name, Tree.val] at he
  split at he
  · rename_i fn hf
    split at he
    · rename_i es vs hw
      have := walk_within (σ := σ) fn.body
      rw [hw] at this
      exact retempVal_uses hF hf (this.1 e he v hv)
    · exact (List.not_mem_nil he).elim
  · exact (List.not_mem_nil he).elim

mutual
/-- **Re-choosing the temporaries keeps the load equations.** -/
theorem loadEqns_retemp (hF : P.Fresh) :
    ∀ (t : Tree) (fp : ℕ), (t.retemp P fs ν fp).loadEqns P = t.loadEqns P
  | .node f σ bufs kids, fp => by
      rw [retemp_node, Tree.loadEqns, Tree.loadEqns, events_retemp hF (bufs' := bufs) (ks' := kids),
        evLoadEqns_retemp hF,
        loadEqnsKids_retemp hF kids _ (length_kidPos_kids (fs := fs) (lp := P.loop) (fp := fp)
          (f := f) (bufs := bufs))]
  | .phantom f σ, fp => by rw [retemp_phantom]

/-- `loadEqns_retemp` for the callees. -/
theorem loadEqnsKids_retemp (hF : P.Fresh) : ∀ (ks : List Tree) (ps : List ℕ), ps.length = ks.length →
    Tree.loadEqnsKids P (Tree.retempKids P fs ν ps ks) = Tree.loadEqnsKids P ks
  | [], ps, _ => by rw [retempKids_nil]
  | k :: ks, p :: ps, h => by
      rw [retempKids_cons, Tree.loadEqnsKids, Tree.loadEqnsKids, loadEqns_retemp hF k p,
        loadEqnsKids_retemp hF ks ps (by simpa using h)]
  | _ :: _, [], h => absurd h (by simp)
end

end Retemp

end
end LeanVM.Guest.Memory
