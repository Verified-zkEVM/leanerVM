/-
  LeanVM.Guest.Memory.EvalB

  Call trees (`Eval.lean`) under any semantics of `BLAKE2S`: an event's check, a valid
  tree and its faithfulness to `Program.RelB`, the deployed ones at `blakeDeployed`.
-/

module

public import LeanVM.Guest.Memory.Eval
public import LeanVM.Guest.CoreB

/-!
# Call trees under any `BLAKE2S` semantics

`Eval.lean`'s trees, events and paths (`Tree`, `Ev`, `walk`, `Tree.eqns`) do not read the
semantics; what does is an event's check, through `Atom.Holds`. Here it is with `S : BlakeSem` a
parameter (`Ev.HoldsB`), and with it every definition and lemma of `Eval.lean` that mentions it:
`Tree.ValidB`, `Tree.KidsValidB`, `Ev.OkB`, `Out.SatB`, `holdsListB_of_walk`, `Tree.ValidB.rel`
(a valid tree is a derivation of `Program.RelB S`), `Tree.ValidB.transfer`,
`Tree.ValidB.eqns_read`, proved as there.

* `validB_deployed`: at `blakeDeployed`, `Tree.ValidB` is `Tree.Valid` (and `ev_holdsB_deployed`,
  `kidsValidB_deployed`, `ev_okB_deployed`, `out_satB_deployed` the same for the others).

This is the Memory layer of the guest's completeness over a completeness model
(`docs/roadmap/t6-completeness.md` §4.2), made as `CoreB.lean` is made from `Core.lean`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

/-! ## The path of a block -/

variable (S) in
/-- What an event checks of the memory and `σ`. -/
def Ev.HoldsB (rd : Reader) (σ : Val) : Ev → Prop
  | .atom a => a.HoldsB S rd σ
  | .inK c => IsInK (σ c)
  | _ => True

/-! ## Valid trees -/

variable (S)
mutual
/-- **An honest evaluation**: `t` runs its function on `args` and returns `rets`, along the path
its valuation takes, every event holding on `rd`. -/
def Tree.ValidB (P : Core.Program) (rd : Reader) : Tree → List E → List E → Prop
  | .node f σ _ kids, args, rets => ∃ fn, P.find? f = some fn ∧ fn.params.map σ = args ∧
      ∃ es vs, walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.HoldsB S rd σ) ∧
        Tree.KidsValidB P rd σ (calls es) kids
  | .phantom .., _, _ => False

/-- The callees of the frames set up: a valid tree for each call entered, a phantom for each
not. -/
def Tree.KidsValidB (P : Core.Program) (rd : Reader) (σ : Val) : List Call → List Tree → Prop
  | [], [] => True
  | c :: cs, k :: ks => k.name = c.f ∧
      (if c.taken then k.ValidB P rd (c.args.map σ) (c.rets.map σ)
        else (∃ f σ', k = .phantom f σ') ∧ Phantom P k (c.args.map σ)) ∧
      Tree.KidsValidB P rd σ cs ks
  | _, _ => False
end
variable {S}

/-! ## Faithfulness to `Program.Rel` -/

section Faithful

variable {C : CallRel} {rd : Reader} {σ : Val}

variable (S) in
/-- An event's check, and a call entered holds of `C`. -/
def Ev.OkB (C : CallRel) (rd : Reader) (σ : Val) (e : Ev) : Prop :=
  e.HoldsB S rd σ ∧ ∀ f args rets, e = .call f args rets → C f (args.map σ) (rets.map σ)

variable (S) in
/-- An outcome's events are `Ok`, and then `next` or the return holds. -/
def Out.SatB (C : CallRel) (rd : Reader) (σ : Val) (next : Prop) (kret : List E → Prop) :
    Out → Prop
  | .fall es => (∀ e ∈ es, e.OkB S C rd σ) ∧ next
  | .ret es vs => (∀ e ∈ es, e.OkB S C rd σ) ∧ kret (vs.map σ)
  | .stuck => False

theorem Out.satB_pre {es : List Ev} {next : Prop} {kret : List E → Prop} :
    ∀ {o : Out}, (o.pre es).SatB S C rd σ next kret ↔ (∀ e ∈ es, e.OkB S C rd σ) ∧ o.SatB S C rd σ next kret
  | .fall _ => by simp only [Out.pre, Out.SatB, List.forall_mem_append, and_assoc]
  | .ret _ _ => by simp only [Out.pre, Out.SatB, List.forall_mem_append, and_assoc]
  | .stuck => by simp [Out.pre, Out.SatB]

theorem pickB_sat {x : V} {args rets : List V} {next : Prop} {kret : List E → Prop} :
    ∀ (fs : List String) (j : ℕ), (pick σ x args rets j fs).SatB S C rd σ next kret →
      (∃ (i : ℕ) (h : i < fs.length), σ x = ofK (gpow (j + i)) ∧
        C fs[i] (args.map σ) (rets.map σ)) ∧ next
  | [], _, h => h.elim
  | f :: fs, j, h => by
      unfold pick at h
      split_ifs at h with hx
      · obtain ⟨he, hn⟩ := h
        exact ⟨⟨0, by simp, by simpa using hx, (he _ (List.mem_singleton_self _)).2 _ _ _ rfl⟩, hn⟩
      · obtain ⟨⟨i, hi, hxi, hc⟩, hn⟩ := pickB_sat fs (j + 1) h
        exact ⟨⟨i + 1, by simpa using hi, by rw [hxi, show j + 1 + i = j + (i + 1) by omega], by simpa using hc⟩, hn⟩

mutual
theorem holdsB_of_walk1 : ∀ (s : Stmt) {next : Prop} {kret : List E → Prop},
    (walk1 σ s).SatB S C rd σ next kret → Stmt.HoldsB S C rd σ s next kret
  | .atom a, _, _, h => by
      simp only [walk1, Out.SatB, List.mem_singleton, forall_eq] at h
      exact ⟨h.1.1, h.2⟩
  | .ite c z n, _, _, h => by
      rw [walk1, Out.satB_pre] at h
      obtain ⟨hc, h⟩ := h
      have hK : IsInK (σ c) := (hc _ (List.mem_singleton_self _)).1
      by_cases h0 : σ c = 0
      · rw [ite_eq_left h0] at h
        exact ⟨hK, fun _ => holdsListB_of_walk z h, fun h' => absurd h0 h'⟩
      · rw [ite_eq_right h0] at h
        exact ⟨hK, fun h' => absurd h' h0, fun _ => holdsListB_of_walk n h⟩
  | .match_ x arms, _, _, h => holdsArmsB_of_walk x arms 0 h
  | .call f args rets, _, _, h => by
      simp only [walk1, Out.SatB, List.mem_singleton, forall_eq] at h
      exact ⟨h.1.2 _ _ _ rfl, h.2⟩
  | .callIf c f args, _, _, h => by
      obtain ⟨he, hn⟩ := h
      refine ⟨(he (.inK c) (by simp)).1, fun h0 => ?_, hn⟩
      have hcall := he (if σ c = 0 then .skip f args else .call f args []) (by simp)
      rw [ite_eq_right h0] at hcall
      exact hcall.2 _ _ _ rfl
  | .dispatch x fs args rets, _, _, h => by
      obtain ⟨⟨i, hi, hx, hc⟩, hn⟩ := pickB_sat fs 0 h
      exact ⟨⟨i, hi, by simpa using hx, hc⟩, hn⟩
  | .ret vs, _, _, h => by
      simp only [walk1, Out.SatB] at h
      exact h.2

theorem holdsListB_of_walk : ∀ (ss : List Stmt) {next : Prop} {kret : List E → Prop},
    (walk σ ss).SatB S C rd σ next kret → Stmt.HoldsListB S C rd σ ss next kret
  | [], _, _, h => h.2
  | s :: ss, next, kret, h => by
      simp only [walk] at h
      refine holdsB_of_walk1 s ?_
      cases hs : walk1 σ s with
      | fall es =>
          simp only [hs, Out.seq, Out.satB_pre] at h
          exact ⟨h.1, holdsListB_of_walk ss h.2⟩
      | ret es vs => simp only [hs, Out.seq] at h; exact h
      | stuck => simp only [hs, Out.seq, Out.SatB] at h

theorem holdsArmsB_of_walk (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {next : Prop}
    {kret : List E → Prop}, (walkArms σ x j arms).SatB S C rd σ next kret →
      Stmt.HoldsArmsB S C rd σ x j arms next kret
  | [], _, _, _, h => h.elim
  | a :: as, j, _, _, h => by
      unfold walkArms at h
      split_ifs at h with hx
      · exact Or.inl ⟨hx, holdsListB_of_walk a h⟩
      · exact Or.inr (holdsArmsB_of_walk x as (j + 1) h)
end

variable {P : Core.Program}

mutual
/-- **A valid tree is a derivation of `Program.RelB`.** -/
theorem Tree.ValidB.rel : ∀ (t : Tree) {args rets : List E}, t.ValidB S P rd args rets →
    P.RelB S rd t.name args rets
  | .node f σ _ kids, args, rets, ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩ =>
      (relB_iff P f args rets).mpr ⟨fn, hf, σ, hp, holdsListB_of_walk fn.body (by
        rw [hw]
        refine ⟨fun e he => ⟨hes e he, fun g a r hg => ?_⟩, hr⟩
        subst hg
        exact Tree.KidsValidB.rel σ kids (calls es) hk _ (mem_calls_of_call he) rfl)⟩
  | .phantom .., _, _, h => h.elim

/-- `Tree.ValidB.rel` for the callees: each call entered holds of `Program.RelB`. -/
theorem Tree.KidsValidB.rel : ∀ (σ : Val) (ks : List Tree) (cs : List Call),
    Tree.KidsValidB S P rd σ cs ks → ∀ c ∈ cs, c.taken = true →
      P.RelB S rd c.f (c.args.map σ) (c.rets.map σ)
  | _, [], [], _, _, hc, _ => (List.not_mem_nil hc).elim
  | σ, k :: ks, c :: cs, ⟨hn, hk, hks⟩, c', hc', ht => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · rw [ite_eq_left ht] at hk
        rw [← hn]
        exact Tree.ValidB.rel k hk
      · exact Tree.KidsValidB.rel σ ks cs hks c' hc' ht
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim
end

end Faithful

/-! ## Memory equations -/

section Transfer

variable {P : Core.Program} {rd rd' : Reader} {σ : Val}

/-- An atom holds on any reader satisfying its equations. -/
theorem holdsB_transfer : ∀ (a : Atom), a.HoldsB S rd σ →
    (∀ q ∈ atomEqns σ a, rd' q.1 = some q.2) → a.HoldsB S rd' σ
  | .const .., h, _ => h
  | .add .., h, _ => h
  | .mul .., h, _ => h
  | .copy .., h, _ => h
  | .load .., h, he => ⟨h.1, he _ (List.mem_singleton_self _)⟩
  | .assertEq .., h, _ => h
  | .assertNe .., h, _ => h
  | .rangeCheck .., h, he =>
      ⟨⟨h.1.1, he _ List.mem_cons_self⟩, h.2.1,
        ⟨h.2.2.1, he _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩⟩
  | .assertInK .., h, _ => h
  | .blake2s .., h, _ => h
  | .frameAddr p run, h, he => by
      refine ⟨h.1, fun k hk w hw => ?_⟩
      have hm : ((σ p).limb 0 * gpow k, σ run[k]) ∈ run.mapIdx fun k v => ((σ p).limb 0 * gpow k, σ v) :=
        List.mem_mapIdx.mpr ⟨k, hk, rfl⟩
      exact Option.some.inj (hw.symm.trans (he _ hm))
  | .hint _, h, _ => h

/-- An atom's equations hold on a memory it holds on, wherever they name an address. -/
theorem atomEqnsB_read {κ : ℕ} (hκ : κ < 64) {L : MemImage κ} :
    ∀ (a : Atom), a.HoldsB S L.read σ → ∀ q ∈ atomEqns σ a, (∃ i : Fin (2 ^ κ), q.1 = gpow i) →
      L.read q.1 = some q.2
  | .load .., h, q, hq, _ => by
      rw [List.mem_singleton.mp hq]
      exact h.2
  | .rangeCheck .., h, q, hq, _ => by
      simp only [atomEqns, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact h.1.2
      · exact h.2.2.2
  | .frameAddr p run, h, q, hq, ⟨i, hi⟩ => by
      obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hq
      dsimp only at hi ⊢
      have := h.2 k hk (L i) (by rw [hi]; exact MemImage.read_gpow hκ L i)
      rw [hi, MemImage.read_gpow hκ L i, this]
  | .const .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .add .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .mul .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .copy .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .assertEq .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .assertNe .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .assertInK .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .blake2s .., _, _, hq, _ => (List.not_mem_nil hq).elim
  | .hint _, _, _, hq, _ => (List.not_mem_nil hq).elim

/-- The events of a path hold on any reader satisfying their equations. -/
theorem eventsB_transfer {es : List Ev} (h : ∀ e ∈ es, e.HoldsB S rd σ)
    (he : ∀ q ∈ evEqns σ es, rd' q.1 = some q.2) : ∀ e ∈ es, e.HoldsB S rd' σ
  | .atom a, hm => holdsB_transfer a (h _ hm) fun q hq => he q (mem_evEqns hm hq)
  | .inK _, hm => h _ hm
  | .call .., _ => trivial
  | .skip .., _ => trivial

/-- The equations of a path hold on a memory its events hold on, wherever they name an
address. -/
theorem evEqnsB_read {κ : ℕ} (hκ : κ < 64) {L : MemImage κ} {es : List Ev}
    (h : ∀ e ∈ es, e.HoldsB S L.read σ) :
    ∀ q ∈ evEqns σ es, (∃ i : Fin (2 ^ κ), q.1 = gpow i) → L.read q.1 = some q.2 := by
  intro q hq hi
  obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp hq
  cases e with
  | atom a => exact atomEqnsB_read hκ a (h _ he) q hq hi
  | inK _ => exact (List.not_mem_nil hq).elim
  | call _ _ _ => exact (List.not_mem_nil hq).elim
  | skip _ _ => exact (List.not_mem_nil hq).elim

mutual
/-- **Transfer**: a valid tree is valid on any reader satisfying its memory equations. -/
theorem Tree.ValidB.transfer : ∀ (t : Tree) {args rets : List E}, t.ValidB S P rd args rets →
    (∀ q ∈ t.eqns P, rd' q.1 = some q.2) → t.ValidB S P rd' args rets
  | .node _ σ _ kids, _, _, ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩, he => by
      rw [eqns_node hf hw] at he
      exact ⟨fn, hf, hp, es, vs, hw, hr,
        eventsB_transfer hes fun q hq => he q (List.mem_append_left _ hq),
        Tree.KidsValidB.transfer σ kids (calls es) hk fun q hq => he q (List.mem_append_right _ hq)⟩
  | .phantom .., _, _, h, _ => h.elim

/-- `Tree.ValidB.transfer` for the callees. -/
theorem Tree.KidsValidB.transfer : ∀ (σ : Val) (ks : List Tree) (cs : List Call),
    Tree.KidsValidB S P rd σ cs ks → (∀ q ∈ Tree.eqnsKids P ks, rd' q.1 = some q.2) →
      Tree.KidsValidB S P rd' σ cs ks
  | _, [], [], _, _ => trivial
  | σ, k :: ks, c :: cs, ⟨hn, hc, hks⟩, he => by
      rw [Tree.eqnsKids] at he
      refine ⟨hn, ?_, Tree.KidsValidB.transfer σ ks cs hks fun q hq => he q (List.mem_append_right _ hq)⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc ⊢
        exact Tree.ValidB.transfer k hc fun q hq => he q (List.mem_append_left _ hq)
      · rw [ite_eq_right ht] at hc ⊢
        exact hc
  | _, [], _ :: _, h, _ => h.elim
  | _, _ :: _, [], h, _ => h.elim
end

mutual
/-- **The equations of a valid tree hold** on the memory it is valid on, wherever they name an
address. -/
theorem Tree.ValidB.eqns_read {κ : ℕ} (hκ : κ < 64) {L : MemImage κ} :
    ∀ (t : Tree) {args rets : List E}, t.ValidB S P L.read args rets → ∀ q ∈ t.eqns P,
      (∃ i : Fin (2 ^ κ), q.1 = gpow i) → L.read q.1 = some q.2
  | .node _ σ _ kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩, q, hq, hi => by
      rw [eqns_node hf hw] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact evEqnsB_read hκ hes q hq hi
      · exact Tree.KidsValidB.eqns_read hκ σ kids (calls es) hk q hq hi
  | .phantom .., _, _, h, _, _, _ => h.elim

/-- `Tree.ValidB.eqns_read` for the callees. -/
theorem Tree.KidsValidB.eqns_read {κ : ℕ} (hκ : κ < 64) {L : MemImage κ} :
    ∀ (σ : Val) (ks : List Tree) (cs : List Call), Tree.KidsValidB S P L.read σ cs ks →
      ∀ q ∈ Tree.eqnsKids P ks, (∃ i : Fin (2 ^ κ), q.1 = gpow i) → L.read q.1 = some q.2
  | _, [], [], _, _, hq, _ => (List.not_mem_nil hq).elim
  | σ, k :: ks, c :: cs, ⟨_, hc, hks⟩, q, hq, hi => by
      rw [Tree.eqnsKids] at hq
      rcases List.mem_append.mp hq with hq | hq
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact Tree.ValidB.eqns_read hκ k hc q hq hi
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          simp [Tree.eqns] at hq
      · exact Tree.KidsValidB.eqns_read hκ σ ks cs hks q hq hi
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim
end

end Transfer

/-! ## At the deployed semantics -/

section Deployed

variable {P : Core.Program} {rd : Reader}

/-- At the deployed semantics, an event's check is `Eval.lean`'s. -/
theorem ev_holdsB_deployed (σ : Val) (e : Ev) : e.HoldsB blakeDeployed rd σ = e.Holds rd σ := by
  cases e <;> simp only [Ev.HoldsB, Ev.Holds, atom_holdsB_deployed]

mutual
/-- **At the deployed semantics, a valid tree is `Eval.lean`'s.** -/
theorem validB_deployed : ∀ (t : Tree) (args rets : List E),
    t.ValidB blakeDeployed P rd args rets = t.Valid P rd args rets
  | .node f σ bufs kids, args, rets => by
      simp only [Tree.ValidB, Tree.Valid, ev_holdsB_deployed, kidsValidB_deployed σ _ kids]
  | .phantom .., _, _ => by simp only [Tree.ValidB, Tree.Valid]

/-- `validB_deployed` for the callees. -/
theorem kidsValidB_deployed (σ : Val) : ∀ (cs : List Call) (ks : List Tree),
    Tree.KidsValidB blakeDeployed P rd σ cs ks = Tree.KidsValid P rd σ cs ks
  | [], [] => by simp only [Tree.KidsValidB, Tree.KidsValid]
  | [], _ :: _ => by simp only [Tree.KidsValidB, Tree.KidsValid]
  | _ :: _, [] => by simp only [Tree.KidsValidB, Tree.KidsValid]
  | c :: cs, k :: ks => by
      simp only [Tree.KidsValidB, Tree.KidsValid, validB_deployed k, kidsValidB_deployed σ cs ks]
end

/-- At the deployed semantics, an event's faithfulness is `Eval.lean`'s. -/
theorem ev_okB_deployed (C : CallRel) (σ : Val) (e : Ev) :
    e.OkB blakeDeployed C rd σ = e.Ok C rd σ := by
  simp only [Ev.OkB, Ev.Ok, ev_holdsB_deployed]

/-- At the deployed semantics, an outcome's satisfaction is `Eval.lean`'s. -/
theorem out_satB_deployed (C : CallRel) (σ : Val) (next : Prop) (kret : List E → Prop) (o : Out) :
    o.SatB blakeDeployed C rd σ next kret = o.Sat C rd σ next kret := by
  cases o <;> simp only [Out.SatB, Out.Sat, ev_okB_deployed]

end Deployed

end
end LeanVM.Guest.Memory
