/-
  LeanVM.Guest.Memory.PlacedB

  Placed relations (`Placed.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.Placed
public import LeanVM.Guest.Memory.TreeB

/-!
# Placed relations under any `BLAKE2S` semantics

`Placed.lean`'s `RelAt` and `KidsFrom`, with `S : BlakeSem` a parameter (`RelAtB`, `KidsFromB`),
and the lemmas about them: `RelAtB.rel`, `kidsValidB_append`, `relAtB_of_walk`,
`relAtB_of_walk_loop`, `placedB_of_pure`, `relAtB_of_rel_pure`. The placement itself
(`Tree.Placed`) is `Placed.lean`'s.

* `relAtB_deployed`, `kidsFromB_deployed`: at `blakeDeployed`, they are `Placed.lean`'s.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

/-! ## What a path places -/

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ)

variable (S) in
/-- **`Program.RelB` placed at `fp`**: a valid tree of `f` on `args`, `rets`, its `HeapBuf`s those
of its paths, placed from `fp`, of `n` words. -/
def RelAtB (rd : Reader) (fp n : ℕ) (f : String) (args rets : List E) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.ValidB S P rd args rets ∧ t.BufsOk P ∧ t.Placed P fs cert fp ∧
    t.total fs = n

variable (S) in
/-- **The callees of the frames `cs` sets up**, their regions one after another from `b`, `n`
words in all: each call entered `RelAtB` its region, each not entered a phantom of its callee's
frame size. -/
def KidsFromB (rd : Reader) (σ : Val) : List Call → ℕ → ℕ → Prop
  | [], _, n => n = 0
  | c :: cs, b, n => ∃ m n', n = m + n' ∧
      (if c.taken then RelAtB S P fs cert rd b m c.f (c.args.map σ) (c.rets.map σ) else m = fs c.f) ∧
      KidsFromB rd σ cs (b + m) n'

variable {P fs cert}

/-- A placed relation is a relation. -/
theorem RelAtB.rel {rd : Reader} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtB S P fs cert rd fp n f args rets) : P.RelB S rd f args rets :=
  let ⟨t, hn, hv, _⟩ := h
  hn ▸ hv.rel t

/-! ## Composing a placed relation -/

section Compose

variable {rd : Reader} {σ : Val}

theorem kidsValidB_append : ∀ {cs : List Call} {ks : List Tree} {cs' : List Call} {ks' : List Tree},
    Tree.KidsValidB S P rd σ cs ks → Tree.KidsValidB S P rd σ cs' ks' →
      Tree.KidsValidB S P rd σ (cs ++ cs') (ks ++ ks')
  | [], [], _, _, _, h' => h'
  | _ :: _, _ :: _, _, _, ⟨hn, hc, h⟩, h' => ⟨hn, hc, kidsValidB_append h h'⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

/-- The callee of one frame: a placed tree of a call entered, a phantom of one not. -/
theorem kidB_of {c : Call} {b m : ℕ} (hc : c.taken = false → P.Takes c.f c.args.length = true)
    (h : if c.taken then RelAtB S P fs cert rd b m c.f (c.args.map σ) (c.rets.map σ) else m = fs c.f) :
    ∃ k : Tree, Tree.KidsValidB S P rd σ [c] [k] ∧ k.BufsOk P ∧ k.Placed P fs cert b ∧
      k.total fs = m := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at h
    obtain ⟨k, hn, hv, hb, hp, htot⟩ := h
    exact ⟨k, ⟨hn, by rw [ite_eq_left ht]; exact hv, trivial⟩, hb, hp, htot⟩
  · rw [ite_eq_right ht] at h
    obtain ⟨σ', hph⟩ := phantom_of_takes (P := P) (f := c.f) (ws := c.args.map σ)
      (by rw [List.length_map]; exact hc (by simpa using ht))
    refine ⟨.phantom c.f σ', ⟨rfl, by rw [ite_eq_right ht]; exact ⟨⟨_, _, rfl⟩, hph⟩, trivial⟩,
      by rw [Tree.BufsOk]; trivial, placed_phantom, by rw [Tree.total, h]⟩

/-- The callees of `KidsFromB`, placed one after another from `b`. -/
theorem kidsB_of_kidsFrom : ∀ (cs : List Call) (b n : ℕ),
    (∀ c ∈ cs, c.taken = false → P.Takes c.f c.args.length = true) →
    KidsFromB S P fs cert rd σ cs b n →
    ∃ ks : List Tree, Tree.KidsValidB S P rd σ cs ks ∧ Tree.BufsOkKids P ks ∧
      Tree.PlacedKids P fs cert (bases b (ks.map (Tree.total fs))) ks ∧
      (ks.map (Tree.total fs)).sum = n
  | [], _, n, _, h => ⟨[], by simp [Tree.KidsValidB], by rw [Tree.BufsOkKids]; trivial,
      placedKids_nil, by rw [KidsFromB] at h; simp [h]⟩
  | c :: cs, b, n, hw, h => by
      rw [KidsFromB] at h
      obtain ⟨m, n', rfl, hc, hcs⟩ := h
      obtain ⟨k, hkv, hkb, hkp, hkt⟩ := kidB_of (hw c List.mem_cons_self) hc
      obtain ⟨ks, hv, hb, hp, hs⟩ :=
        kidsB_of_kidsFrom cs (b + m) n' (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) hcs
      refine ⟨k :: ks, ⟨hkv.1, hkv.2.1, hv⟩, by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, ?_, ?_⟩
      · rw [List.map_cons, bases, placedKids_cons, hkt]
        exact ⟨hkp, hp⟩
      · rw [List.map_cons, List.sum_cons, hkt, hs]

/-- **Composition**, a function that is not a loop helper (or whose path calls nothing): its
parameters, its path, its `HeapBuf` pointers from `fp + fs f`, its `frameAddr`s in its frame, and
its callees one after another from the end of its `HeapBuf`s give it `RelAtB fp`, of its frame,
`HeapBuf`s and callees' words. -/
theorem relAtB_of_walk (hP : P.Wf) {fp N : ℕ} {f : String} {args rets : List E} {fn : Fn}
    {es : List Ev} {vs : List V} (hf : P.find? f = some fn) (hl : P.loop f = false ∨ calls es = [])
    (hp : fn.params.map σ = args) (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets)
    (hes : ∀ e ∈ es, e.HoldsB S rd σ)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromB S P fs cert rd σ (calls es) (fp + fs f + (allocs σ es).sum) N) :
    RelAtB S P fs cert rd fp (fs f + (allocs σ es).sum + N) f args rets := by
  obtain ⟨ks, hkv, hkb, hkp, hks⟩ :=
    kidsB_of_kidsFrom _ _ _ (takes_of_calls hP (List.mem_of_find?_eq_some hf) hw) hk
  have hl' : P.loop f = false ∨ ks.map (Tree.total fs) = [] := by
    rcases hl with hl | hl
    · exact Or.inl hl
    · rw [hl] at hkv
      cases ks with
      | nil => exact Or.inr rfl
      | cons _ _ => exact hkv.elim
  obtain ⟨hbb, hkpos⟩ := kidPos_not_loop (fs := fs) (fp := fp) (bufs := allocs σ es) hl'
  refine ⟨.node f σ (allocs σ es) ks, rfl, ⟨fn, hf, hp, es, vs, hw, hr, hes, hkv⟩, ?_, ?_, ?_⟩
  · rw [Tree.BufsOk, events_node hf hw]
    exact ⟨rfl, hkb⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    exact ⟨⟨hbuf, haddr⟩, hkp⟩
  · rw [total_node, totalKids_eq_sum, hks]
    omega

/-- **Composition**, a loop helper: as `relAtB_of_walk`, its tail call (its last) first, at
`fp + fs f`, of `m` words, then its `HeapBuf`s from `fp + fs f + m`, then its other callees. -/
theorem relAtB_of_walk_loop (hP : P.Wf) {fp m N : ℕ} {f : String} {args rets : List E} {fn : Fn}
    {es : List Ev} {vs : List V} {cs : List Call} {c : Call} (hf : P.find? f = some fn)
    (hl : P.loop f = true) (hp : fn.params.map σ = args) (hw : walk σ fn.body = .ret es vs)
    (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.HoldsB S rd σ) (hc : calls es = cs ++ [c])
    (htail : if c.taken then RelAtB S P fs cert rd (fp + fs f) m c.f (c.args.map σ) (c.rets.map σ)
      else m = fs c.f)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f + m) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromB S P fs cert rd σ cs (fp + fs f + m + (allocs σ es).sum) N) :
    RelAtB S P fs cert rd fp (fs f + m + (allocs σ es).sum + N) f args rets := by
  have htk := takes_of_calls hP (List.mem_of_find?_eq_some hf) hw
  rw [hc] at htk
  obtain ⟨ks, hkv, hkb, hkp, hks⟩ := kidsB_of_kidsFrom _ _ _
    (fun c' hc' => htk c' (List.mem_append_left _ hc')) hk
  obtain ⟨k, hkv', hkb', hkp', hkt⟩ :=
    kidB_of (htk c (List.mem_append_right _ List.mem_cons_self)) htail
  have hns : (ks ++ [k]).map (Tree.total fs) = ks.map (Tree.total fs) ++ [m] := by
    rw [List.map_append, List.map_singleton, hkt]
  have hbb : bufBase fs P.loop fp f ((ks ++ [k]).map (Tree.total fs)) = fp + fs f + m := by
    rw [hns]; simp [bufBase, hl]
  have hkpos : kidPos fs P.loop fp f (allocs σ es) ((ks ++ [k]).map (Tree.total fs)) =
      bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs)) ++ [fp + fs f] := by
    rw [kidPos, ite_eq_left hl, hbb, hns, List.dropLast_concat, List.getLast?_concat]
    rfl
  refine ⟨.node f σ (allocs σ es) (ks ++ [k]), rfl,
    ⟨fn, hf, hp, es, vs, hw, hr, hes, by rw [hc]; exact kidsValidB_append hkv hkv'⟩, ?_, ?_, ?_⟩
  · rw [Tree.BufsOk, events_node hf hw]
    refine ⟨rfl, bufsOkKids_append hkb ?_⟩
    rw [Tree.BufsOkKids, Tree.BufsOkKids]
    exact ⟨hkb', trivial⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    refine ⟨⟨hbuf, haddr⟩, placedKids_append (by rw [length_bases, List.length_map]) hkp ?_⟩
    rw [placedKids_cons]
    exact ⟨hkp', placedKids_nil⟩
  · rw [total_node, totalKids_eq_sum, hns, List.sum_append, hks]
    simp only [List.sum_cons, List.sum_nil]
    omega

end Compose

/-! ## Subtrees with nothing to place -/

section Pure

variable {Sz : List String} {σ : Val}

variable {rd : Reader}

mutual
/-- A valid tree of a function of a pure set is placed anywhere. -/
theorem placedB_of_pure (hS : P.PureIn Sz) : ∀ (t : Tree) {args rets : List E},
    t.ValidB S P rd args rets → t.BufsOk P → t.name ∈ Sz → ∀ fp, t.Placed P fs cert fp
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hb, hn, fp => by
      have hpure : ∀ e ∈ es, e.pure Sz := by
        have := walk_pure (σ := σ) fn.body (hS f hn fn hf)
        rwa [hw] at this
      rw [Tree.BufsOk, events_node hf hw, allocs_pure hpure] at hb
      obtain ⟨rfl, hkb⟩ := hb
      rw [placed_node, events_node hf hw]
      refine ⟨⟨by rw [allocDsts_pure hpure]; rfl, fun q hq => by
        rw [addrs_pure hpure] at hq; exact (List.not_mem_nil hq).elim⟩, ?_⟩
      exact placedKidsB_of_pure hS kids σ (calls es) hk hkb (calls_pure hpure) _
  | .phantom .., _, _, h, _, _, _ => h.elim

/-- `placedB_of_pure` for the callees. -/
theorem placedKidsB_of_pure (hS : P.PureIn Sz) : ∀ (ks : List Tree) (σ : Val) (cs : List Call),
    Tree.KidsValidB S P rd σ cs ks → Tree.BufsOkKids P ks → (∀ c ∈ cs, c.f ∈ Sz) →
      ∀ ps, Tree.PlacedKids P fs cert ps ks
  | [], _, _, _, _, _, _ => placedKids_nil
  | _ :: _, _, _, _, _, _, [] => by rw [Tree.PlacedKids]; trivial
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hb, hS', p :: ps => by
      rw [Tree.BufsOkKids] at hb
      rw [placedKids_cons]
      refine ⟨?_, placedKidsB_of_pure hS ks σ cs hks hb.2
        (fun c' hc' => hS' c' (List.mem_cons_of_mem _ hc')) ps⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact placedB_of_pure hS k hc hb.1 (hn ▸ hS' c List.mem_cons_self) p
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact placed_phantom
  | _ :: _, _, [], h, _, _, _ :: _ => h.elim
end

/-- **A function of a pure set is placed anywhere**: in a well-formed program, `Program.RelB`
gives `RelAtB` at every frame pointer, of one size. -/
theorem relAtB_of_rel_pure (hP : P.Wf) (hS : P.PureIn Sz) {g : String} (hg : g ∈ Sz)
    {args rets : List E} (h : P.RelB S rd g args rets) :
    ∃ n, ∀ fp, RelAtB S P fs cert rd fp n g args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.RelB.tree hP h
  exact ⟨t.total fs, fun fp => ⟨t, hn, hv, hb, placedB_of_pure hS t hv hb (hn ▸ hg) fp, rfl⟩⟩

end Pure

/-! ## At the deployed semantics -/

section Deployed

variable {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader}

/-- At the deployed semantics, `RelAtB` is `Placed.lean`'s `RelAt`. -/
theorem relAtB_deployed (fp n : ℕ) (f : String) (args rets : List E) :
    RelAtB blakeDeployed P fs cert rd fp n f args rets = RelAt P fs cert rd fp n f args rets := by
  simp only [RelAtB, RelAt, validB_deployed]

/-- At the deployed semantics, `KidsFromB` is `Placed.lean`'s `KidsFrom`. -/
theorem kidsFromB_deployed (σ : Val) : ∀ (cs : List Call) (b n : ℕ),
    KidsFromB blakeDeployed P fs cert rd σ cs b n = KidsFrom P fs cert rd σ cs b n
  | [], _, _ => by simp only [KidsFromB, KidsFrom]
  | c :: cs, b, n => by simp only [KidsFromB, KidsFrom, relAtB_deployed, kidsFromB_deployed σ cs]

end Deployed

end
end LeanVM.Guest.Memory
