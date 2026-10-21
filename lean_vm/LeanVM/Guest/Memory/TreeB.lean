/-
  LeanVM.Guest.Memory.TreeB

  Every derivation of `Program.RelB` is a valid tree (`Tree.lean`) under any semantics of
  `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.Tree
public import LeanVM.Guest.Memory.EvalB

/-!
# Trees of derivations under any `BLAKE2S` semantics

`Tree.lean`'s converse with `S : BlakeSem` a parameter: a block that holds under `S` has an
outcome satisfying it (`walkB_sat`), so in a well-formed program every derivation of
`Program.RelB S` is a valid tree (`relNB_tree`, `Program.RelB.tree`, `relB_iff_tree`). The
well-formedness and the allocation sizes (`Program.Wf`, `Tree.BufsOk`) are `Tree.lean`'s.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

/-! ## The walk of a block that holds -/

section Converse

variable {C : CallRel} {rd : Reader} {σ : Val} {P : Core.Program}

theorem pickB_sat_of {x : V} {args rets : List V} {next : Prop} {kret : List E → Prop} :
    ∀ (fs : List String) (j : ℕ), j + fs.length ≤ 2 ^ 64 - 1 →
      (∃ (i : ℕ) (h : i < fs.length), σ x = ofK (gpow (j + i)) ∧
        C fs[i] (args.map σ) (rets.map σ)) → next → (pick σ x args rets j fs).SatB S C rd σ next kret
  | [], _, _, ⟨i, hi, _⟩, _ => absurd hi (by simp)
  | f :: fs, j, hb, ⟨i, hi, hx, hc⟩, hn => by
      simp only [List.length_cons] at hb hi
      unfold pick
      split_ifs with hxj
      · obtain rfl : i = 0 := by
          by_contra h0
          exact ofK_gpow_ne (show j < j + i by omega) (by omega) (hxj.symm.trans hx)
        refine ⟨fun e he => ?_, hn⟩
        rw [List.mem_singleton] at he
        subst he
        exact ⟨trivial, fun g a r he => by cases he; simpa using hc⟩
      · cases i with
        | zero => exact absurd (by simpa using hx) hxj
        | succ i =>
            exact pickB_sat_of fs (j + 1) (by omega)
              ⟨i, by omega, by rw [hx]; congr 2; omega, by simpa using hc⟩ hn

mutual
/-- **The converse of `holdsB_of_walk1`**: a well-formed statement that holds has a satisfied
walk. -/
theorem walk1B_sat : ∀ (s : Stmt), Stmt.wf P s = true → ∀ {next : Prop} {kret : List E → Prop},
    Stmt.HoldsB S C rd σ s next kret → (walk1 σ s).SatB S C rd σ next kret
  | .atom a, _, _, _, h => by
      simp only [walk1, Out.SatB, List.mem_singleton, forall_eq]
      exact ⟨⟨h.1, fun _ _ _ h => nomatch h⟩, h.2⟩
  | .ite c z n, hw, _, _, h => by
      simp only [Stmt.wf, Bool.and_eq_true] at hw
      rw [walk1, Out.satB_pre]
      refine ⟨fun e he => ?_, ?_⟩
      · rw [List.mem_singleton] at he
        subst he
        exact ⟨h.1, fun _ _ _ h => nomatch h⟩
      · by_cases h0 : σ c = 0
        · rw [ite_eq_left h0]
          exact walkB_sat z hw.1 (h.2.1 h0)
        · rw [ite_eq_right h0]
          exact walkB_sat n hw.2 (h.2.2 h0)
  | .match_ x arms, hw, _, _, h => by
      simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
      exact walkArmsB_sat x arms 0 (by omega) hw.2 h
  | .call f args rets, _, _, _, h => by
      simp only [walk1, Out.SatB, List.mem_singleton, forall_eq]
      exact ⟨⟨trivial, fun g a r he => by cases he; exact h.1⟩, h.2⟩
  | .callIf c f args, _, _, _, h => by
      rw [walk1]
      refine ⟨fun e he => ?_, h.2.2⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨h.1, fun _ _ _ h => nomatch h⟩
      · by_cases h0 : σ c = 0
        · rw [ite_eq_left h0]
          exact ⟨trivial, fun _ _ _ h => nomatch h⟩
        · rw [ite_eq_right h0]
          exact ⟨trivial, fun g a r he => by cases he; exact h.2.1 h0⟩
  | .dispatch x fs args rets, hw, _, _, h => by
      simp only [Stmt.wf, decide_eq_true_eq] at hw
      obtain ⟨⟨i, hi, hx, hc⟩, hn⟩ := h
      exact pickB_sat_of fs 0 (by omega) ⟨i, hi, by simpa using hx, hc⟩ hn
  | .ret vs, _, _, _, h => by
      rw [walk1]
      exact ⟨fun _ he => (List.not_mem_nil he).elim, h⟩

/-- **The converse of `holdsListB_of_walk`**: a well-formed block that holds has a satisfied
walk. -/
theorem walkB_sat : ∀ (ss : List Stmt), Stmt.wfList P ss = true →
    ∀ {next : Prop} {kret : List E → Prop},
    Stmt.HoldsListB S C rd σ ss next kret → (walk σ ss).SatB S C rd σ next kret
  | [], _, _, _, h => by
      rw [walk]
      exact ⟨fun _ he => (List.not_mem_nil he).elim, h⟩
  | s :: ss, hw, _, _, h => by
      simp only [Stmt.wfList, Bool.and_eq_true] at hw
      have hs := walk1B_sat s hw.1 h
      rw [walk]
      cases hs' : walk1 σ s with
      | fall es =>
          rw [hs'] at hs
          rw [Out.seq, Out.satB_pre]
          exact ⟨hs.1, walkB_sat ss hw.2 hs.2⟩
      | ret es vs =>
          rw [hs'] at hs
          exact hs
      | stuck =>
          rw [hs'] at hs
          exact hs.elim

/-- **The converse of `holdsArmsB_of_walk`**: the arm that holds is the first at its power of
`g`. -/
theorem walkArmsB_sat (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    j + arms.length ≤ 2 ^ 64 - 1 → Stmt.wfArms P arms = true →
    ∀ {next : Prop} {kret : List E → Prop},
    Stmt.HoldsArmsB S C rd σ x j arms next kret → (walkArms σ x j arms).SatB S C rd σ next kret
  | [], _, _, _, _, _, h => by simp [Stmt.HoldsArmsB] at h
  | a :: as, j, hb, hw, _, _, h => by
      simp only [Stmt.wfArms, Bool.and_eq_true] at hw
      simp only [List.length_cons] at hb
      unfold walkArms
      split_ifs with hx
      · rcases h with ⟨-, ha⟩ | h
        · exact walkB_sat a hw.1 ha
        · obtain ⟨i, hi, hxi, -⟩ := (holdsArmsB_iff x as (j + 1) _ _).mp h
          exact absurd (hx.symm.trans hxi) (ofK_gpow_ne (by omega) (by omega))
      · rcases h with ⟨hx', -⟩ | h
        · exact absurd hx' hx
        · exact walkArmsB_sat x as (j + 1) (by omega) hw.2 h
end

end Converse

/-! ## The call tree of a derivation -/

section Tree

variable {P : Core.Program} {rd : Reader}

/-- The callees of a path whose calls hold of `P.relNB rd n`, given trees for those. -/
theorem kidsB_of_events {n : ℕ} {σ : Val}
    (ih : ∀ f args rets, P.relNB S rd n f args rets →
      ∃ t : Tree, t.name = f ∧ t.ValidB S P rd args rets ∧ t.BufsOk P) :
    ∀ es : List Ev, (∀ e ∈ es, e.OkB S (P.relNB S rd n) rd σ) → (∀ e ∈ es, e.Wf P) →
      ∃ ks, Tree.KidsValidB S P rd σ (calls es) ks ∧ Tree.BufsOkKids P ks
  | [], _, _ => ⟨[], by simp [calls, Tree.KidsValidB], trivial⟩
  | e :: es, ho, hw => by
      obtain ⟨ks, hk, hb⟩ := kidsB_of_events ih es (fun e he => ho e (List.mem_cons_of_mem _ he))
        (fun e he => hw e (List.mem_cons_of_mem _ he))
      have ho := ho e List.mem_cons_self
      have hw := hw e List.mem_cons_self
      cases e with
      | atom _ => exact ⟨ks, by simpa [calls, List.filterMap_cons, Ev.call?] using hk, hb⟩
      | inK _ => exact ⟨ks, by simpa [calls, List.filterMap_cons, Ev.call?] using hk, hb⟩
      | call f args rets =>
          obtain ⟨t, hn, hv, htb⟩ := ih f _ _ (ho.2 f args rets rfl)
          refine ⟨t :: ks, ?_, htb, hb⟩
          simp only [calls, List.filterMap_cons, Ev.call?]
          exact ⟨hn, by simpa using hv, by simpa [calls] using hk⟩
      | skip f args =>
          obtain ⟨σ', hph⟩ := phantom_of_takes (ws := args.map σ) (by rw [List.length_map]; exact hw)
          refine ⟨.phantom f σ' :: ks, ?_, trivial, hb⟩
          simp only [calls, List.filterMap_cons, Ev.call?]
          exact ⟨rfl, by simpa using hph, by simpa [calls] using hk⟩

/-- **A derivation of `Program.relNB` is a valid tree**, of a well-formed program. -/
theorem relNB_tree (hP : P.Wf) : ∀ (n : ℕ) (f : String) (args rets : List E),
    P.relNB S rd n f args rets → ∃ t : Tree, t.name = f ∧ t.ValidB S P rd args rets ∧ t.BufsOk P
  | 0, _, _, _, h => h.elim
  | n + 1, f, args, rets, ⟨fn, hf, σ, hp, hb⟩ => by
      have hwf := hP fn (List.mem_of_find?_eq_some hf)
      have hs := walkB_sat (C := P.relNB S rd n) fn.body hwf hb
      have ha := walk_wf (σ := σ) fn.body hwf
      cases hwk : walk σ fn.body with
      | fall es =>
          rw [hwk] at hs
          exact hs.2.elim
      | stuck =>
          rw [hwk] at hs
          exact hs.elim
      | ret es vs =>
          rw [hwk] at hs ha
          obtain ⟨ks, hk, hkb⟩ := kidsB_of_events (relNB_tree hP n) es hs.1 ha
          refine ⟨.node f σ (allocs σ es) ks, rfl,
            ⟨fn, hf, hp, es, vs, hwk, hs.2, fun e he => (hs.1 e he).1, hk⟩, ?_⟩
          rw [Tree.BufsOk, events_node hf hwk]
          exact ⟨rfl, hkb⟩

/-- **A derivation of `Program.RelB` is a valid tree** of a well-formed program: a call tree of
`f` on its argument and return words, every instance's `HeapBuf`s those of its path and every
untaken `callIf` a phantom holding the words written. -/
theorem _root_.LeanVM.Guest.Core.Program.RelB.tree (hP : P.Wf) {f : String} {args rets : List E}
    (h : P.RelB S rd f args rets) :
    ∃ t : Tree, t.name = f ∧ t.ValidB S P rd args rets ∧ t.BufsOk P :=
  let ⟨n, hn⟩ := h
  relNB_tree hP n f args rets hn

/-- **`Program.RelB` is the valid trees** of a well-formed program. -/
theorem relB_iff_tree (hP : P.Wf) {f : String} {args rets : List E} :
    P.RelB S rd f args rets ↔ ∃ t : Tree, t.name = f ∧ t.ValidB S P rd args rets :=
  ⟨fun h => let ⟨t, hn, hv, _⟩ := Program.RelB.tree hP h; ⟨t, hn, hv⟩,
    fun ⟨t, hn, hv⟩ => hn ▸ hv.rel t⟩

end Tree

end
end LeanVM.Guest.Memory
