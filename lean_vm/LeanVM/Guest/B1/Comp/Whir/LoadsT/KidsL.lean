/-
  LeanVM.Guest.B1.Comp.Whir.LoadsT.KidsL

  The stacked opening's stream-reading callees, over every valid tree under any semantics: where
  they leave the cursor and which words they load.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.LoadsL
public import LeanVM.Guest.B1.FiatShamir
public import LeanVM.Guest.B1.Opening

/-!
# `opening_fold` and `opening_final_message`, loading what they read

Over every valid tree under any semantics `S` (no hash enters):

* `osL_node`: a valid tree of a straight-line function is its node, its path the body's events
  holding, its returns the body's returned values;
* `osL_fold`: `opening_fold` returns the cursor two words on and loads the two words at it;
* `osL_validB_read`: a valid tree's memory satisfies its load equations; `osL_kidOf`: the callee
  tree of an entered call;
* `osL_fm`: a function with body `ofmBody n` (`opening_final_message__L{n}`) returns the cursor
  `n` words on and loads the `n` words at it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {S : BlakeSem} {rd : Reader}

/-- **A valid tree of a straight-line function**: its node at a valuation of its parameters, its
path the body's events holding, its returns the returned values. -/
theorem osL_node {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Main.Stmt.straight = true) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.ValidB S coreProgram rd args rets) :
    ∃ σ bufs kids, t = Memory.Tree.node f σ bufs kids ∧ fn.params.map σ = args ∧
      walk σ fn.body = .ret (pre.flatMap (Main.slEvs σ)) vs ∧ vs.map σ = rets ∧
      (∀ e ∈ pre.flatMap (Main.slEvs σ), e.HoldsB S rd σ) ∧
      Tree.KidsValidB S coreProgram rd σ ((pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) kids := by
  match t, hn, hv with
  | .node g σ bufs kids, hn, hv =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn', hf', hp, es, vs', hw, hr, hes, hk⟩ := hv
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    have hw' : walk σ fn.body = .ret (pre.flatMap (Main.slEvs σ)) vs := by
      rw [hb]; exact Main.walk_straight σ vs pre hst
    rw [hw'] at hw
    cases hw
    obtain ⟨-, -, -, i4⟩ := Main.straight_parts σ pre hst
    exact ⟨σ, bufs, kids, rfl, hp, hw', hr, hes, by rw [← i4]; exact hk⟩

/-! ## `opening_fold` -/

/-- `opening_fold`'s statements before its `ret`. -/
noncomputable def osLFoldPre : List Stmt := (Fn.body Data.core8).take 55

set_option maxRecDepth 100000 in
theorem osL_fold_body : Fn.body Data.core8 =
    osLFoldPre ++ [.ret [.n 56, .n 57, .n 60, .n 61, .n 62, .n 63, .n 64]] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osL_fold_straight : osLFoldPre.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osL_fold_atoms :
    stmtsEqb [.atom (.load (.n 26) (.n 2) 0)] ((osLFoldPre.drop 20).take 1) = true ∧
    stmtsEqb [.atom (.load (.n 41) (.n 2) 1)] ((osLFoldPre.drop 33).take 1) = true ∧
    stmtsEqb [.atom (.const (.n 58) (word 4 0 0))] ((osLFoldPre.drop 48).take 1) = true ∧
    stmtsEqb [.atom (.mul (.n 59) (.n 2) (.n 58))] ((osLFoldPre.drop 49).take 1) = true ∧
    stmtsEqb [.atom (.copy (.n 60) (.n 59))] ((osLFoldPre.drop 50).take 1) = true := by
  decide +kernel

/-- **Every valid tree of `opening_fold`** returns its cursor two words on and loads the two
words at it. -/
theorem osL_fold {t : Tree} {args rets : List E} (hn : t.name = "opening_fold")
    (hv : t.ValidB S coreProgram rd args rets) :
    rets.getD 2 0 = args.getD 2 0 * gen ^ 2 ∧
      ∀ j < 2, ∃ v, ((args.getD 2 0).limb 0 * Parameters.gpow j, v) ∈ t.loadEqns coreProgram := by
  obtain ⟨σ, bufs, kids, rfl, hp, hw, hr, hes, -⟩ :=
    osL_node (S := S) find_opening_fold osL_fold_body osL_fold_straight hn hv
  obtain ⟨l0, l1, c58, m59, c60⟩ := osL_fold_atoms
  have hpre : ∀ a, Stmt.atom a ∈ osLFoldPre → a.HoldsB S rd σ :=
    fun a ha => hes _ (mem_slEvs_of ha)
  have a58 := hpre _ (mem_of_stmtsEqb c58)
  have a59 := hpre _ (mem_of_stmtsEqb m59)
  have a60 := hpre _ (mem_of_stmtsEqb c60)
  simp only [Atom.HoldsB, word_four] at a58 a59 a60
  rw [core8_params] at hp
  have h2 : args.getD 2 0 = σ (.n 2) := by rw [← hp]; rfl
  refine ⟨?_, fun j hj => ?_⟩
  · rw [← hr, h2]
    show σ (.n 60) = _
    rw [a60, a59, a58]
  · rw [h2]
    interval_cases j
    · exact ⟨_, mem_loadEqns_node find_opening_fold hw (mem_evLoadEqns (mem_slEvs_of (mem_of_stmtsEqb l0)))⟩
    · exact ⟨_, mem_loadEqns_node find_opening_fold hw (mem_evLoadEqns (mem_slEvs_of (mem_of_stmtsEqb l1)))⟩

/-! ## `opening_final_message` -/

theorem ofm_dropLast (n : ℕ) : (ofmBody n).dropLast = [.atom (.copy (.n 4) (.n 0)), .atom (.copy (.n 5) (.n 1))] ++
    ((List.range n).map ofmBlock).flatten ++ (ofmTail n).dropLast := by
  rw [ofmBody, List.dropLast_append_of_ne_nil (by simp [ofmTail])]

theorem ofmBody_eq (n : ℕ) : ofmBody n = ((ofmBody n).dropLast) ++
    [.ret [.n (6 + 15 * n), .n (7 + 15 * n), .n (10 + 15 * n)]] := by
  rw [ofm_dropLast]
  simp [ofmBody, ofmTail]

theorem ofmBlock_straight (i : ℕ) : (ofmBlock i).all Main.Stmt.straight = true := by
  simp only [ofmBlock, List.all_append]
  rfl

theorem ofm_straight (n : ℕ) : (ofmBody n).dropLast.all Main.Stmt.straight = true := by
  rw [ofm_dropLast, List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨rfl, ?_⟩, rfl⟩
  rw [List.all_eq_true]
  intro s hs
  obtain ⟨l, hl, hs⟩ := List.mem_flatten.mp hs
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hl
  exact List.all_eq_true.mp (ofmBlock_straight i) s hs

/-- **Every valid tree of a function with body `ofmBody n`** (`opening_final_message__L{n}`)
returns its cursor `n` words on and loads the `n` words at it. -/
theorem osL_fm {name : String} {fn : Fn} (n : ℕ) (hn64 : n < 64) (hfind : coreProgram.find? name = some fn)
    (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : fn.body = ofmBody n) {t : Tree}
    {args rets : List E} (hn : t.name = name) (hv : t.ValidB S coreProgram rd args rets) :
    rets.getD 2 0 = args.getD 2 0 * gen ^ n ∧
      ∀ j < n, ∃ v, ((args.getD 2 0).limb 0 * Parameters.gpow j, v) ∈ t.loadEqns coreProgram := by
  have hb : fn.body = (ofmBody n).dropLast ++ [.ret [.n (6 + 15 * n), .n (7 + 15 * n), .n (10 + 15 * n)]] := by
    rw [hbody]; exact ofmBody_eq n
  obtain ⟨σ, bufs, kids, rfl, hp, hw, hr, hes, -⟩ := osL_node (S := S) hfind hb (ofm_straight n) hn hv
  have hpre : ∀ a, Stmt.atom a ∈ (ofmBody n).dropLast → a.HoldsB S rd σ :=
    fun a ha => hes _ (mem_slEvs_of ha)
  rw [hparams] at hp
  have h2 : args.getD 2 0 = σ (.n 2) := by rw [← hp]; rfl
  refine ⟨?_, fun j hj => ?_⟩
  · have tl : ∀ a, Stmt.atom a ∈ (ofmTail n).dropLast → Stmt.atom a ∈ (ofmBody n).dropLast :=
      fun a h => by rw [ofm_dropLast]; exact List.mem_append_right _ h
    have t1 := hpre (.const (.n (8 + 15 * n)) (word (2 ^ n) 0 0)) (tl _ (by simp [ofmTail]))
    have t2 := hpre (.mul (.n (9 + 15 * n)) (.n 2) (.n (8 + 15 * n))) (tl _ (by simp [ofmTail]))
    have t3 := hpre (.copy (.n (10 + 15 * n)) (.n (9 + 15 * n))) (tl _ (by simp [ofmTail]))
    simp only [Atom.HoldsB] at t1 t2 t3
    rw [← hr, h2]
    show σ (.n (10 + 15 * n)) = _
    rw [t3, t2, t1, word_pow_two hn64]
  · rw [h2]
    have hm : Stmt.atom (.load (.n (6 + 15 * j)) (.n 2) j) ∈ (ofmBody n).dropLast := by
      rw [ofm_dropLast]
      refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr
        ⟨ofmBlock j, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ?_⟩))
      simp [ofmBlock, fsNextT]
    exact ⟨_, mem_loadEqns_node hfind hw (mem_evLoadEqns (mem_slEvs_of hm))⟩

section
variable {S : BlakeSem} {P : Core.Program} {rd : Reader}

theorem osL_evLoadEqns_read {σ : Val} {es : List Ev} (hes : ∀ e ∈ es, e.HoldsB S rd σ) :
    ∀ q ∈ evLoadEqns σ es, rd q.1 = some q.2 := by
  intro q hq
  obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp hq
  match e, hq, hes e he with
  | .atom (.load d p off), hq, h => rw [List.mem_singleton.mp hq]; exact h.2

mutual
/-- **A valid tree's memory satisfies its load equations.** -/
theorem osL_validB_read : ∀ (t : Tree) {args rets : List E}, t.ValidB S P rd args rets →
    ∀ q ∈ t.loadEqns P, rd q.1 = some q.2
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩ => by
      intro q hq
      rw [Tree.loadEqns, events_node hf hw, List.mem_append] at hq
      rcases hq with hq | hq
      · exact osL_evLoadEqns_read hes q hq
      · exact osL_kidsValidB_read _ _ hk q hq
  | .phantom .., _, _, h => h.elim

/-- `osL_validB_read` of the callees. -/
theorem osL_kidsValidB_read {σ : Val} : ∀ (cs : List Call) (ks : List Tree),
    Tree.KidsValidB S P rd σ cs ks → ∀ q ∈ Tree.loadEqnsKids P ks, rd q.1 = some q.2
  | [], [], _, q, hq => by rw [Tree.loadEqnsKids] at hq; exact absurd hq List.not_mem_nil
  | c :: cs, k :: ks, ⟨_, hv, hks⟩, q, hq => by
      rw [Tree.loadEqnsKids, List.mem_append] at hq
      rcases hq with hq | hq
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hv
          exact osL_validB_read k hv q hq
        · rw [ite_eq_right ht] at hv
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hv
          rw [Tree.loadEqns] at hq
          exact absurd hq List.not_mem_nil
      · exact osL_kidsValidB_read cs ks hks q hq
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
end

/-- The callee tree of an entered call. -/
theorem osL_kidOf {σ : Val} : ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValidB S P rd σ cs ks →
    ∀ c ∈ cs, c.taken = true → ∃ k ∈ ks, k.name = c.f ∧ k.ValidB S P rd (c.args.map σ) (c.rets.map σ)
  | [], _, _, c, hc, _ => absurd hc List.not_mem_nil
  | _ :: _, [], hv, _, _, _ => hv.elim
  | c1 :: cs, k :: ks, hv, c, hc, ht => by
    obtain ⟨hn, hv1, hks⟩ := hv
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [ite_eq_left ht] at hv1
      exact ⟨k, List.mem_cons_self, hn, hv1⟩
    · obtain ⟨k', hk', h1, h2⟩ := osL_kidOf hks c hc ht
      exact ⟨k', List.mem_cons_of_mem _ hk', h1, h2⟩

end

end
end LeanVM.Guest.B1
