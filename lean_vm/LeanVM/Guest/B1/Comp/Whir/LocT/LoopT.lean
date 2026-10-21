/-
  LeanVM.Guest.B1.Comp.Whir.LocT.LoopT

  `relAtInB_of_walk_loop` with predicates: a loop helper's node, its tail's tree satisfying a
  predicate, satisfies any predicate the tail's gives it.
-/

module

public import LeanVM.Guest.B1.Comp.TreeRoot

/-!
# A loop helper's step with predicates

`relAtInBT_of_walk_loop`: `Memory.relAtInB_of_walk_loop` where the tail call's relation holds by a
tree satisfying `Qt` (`RelAtInBT`), and the node, with any callees valid for the other calls and the
tail's tree, satisfies `Q`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader} {σ : Val}

theorem RelAtInBT.toB {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E} {Q : Tree → Prop}
    (h : RelAtInBT S fs cert rd R D fp n f args rets Q) : RelAtInB S coreProgram fs cert rd R D fp n f args rets :=
  let ⟨t, _, h1, h2, h3, h4, h5, h6, h7⟩ := h
  ⟨t, h1, h2, h3, h4, h5, h6, h7⟩

/-- The tail callee of `relAtInBT_of_walk_loop`: its tree satisfying `Qt` when entered. -/
theorem kidBT_ofIn {c : Call} {b m : ℕ} {Rk Dk : ℕ → Prop} {Qt : Tree → Prop}
    (hc : c.taken = false → coreProgram.Takes c.f c.args.length = true)
    (h : if c.taken then RelAtInBT S fs cert rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ) Qt
      else m = fs c.f) :
    ∃ k : Tree, Tree.KidsValidB S coreProgram rd σ [c] [k] ∧ k.BufsOk coreProgram ∧
      k.Placed coreProgram fs cert b ∧ k.total fs = m ∧ k.LoadsIn coreProgram fs cert Rk b ∧
      (c.taken = true → ∀ i, Dk i → k.Data coreProgram fs cert b i) ∧ (c.taken = true → Qt k) := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at h
    obtain ⟨k, hq, hn, hv, hb, hp, htot, hl, hd⟩ := h
    exact ⟨k, ⟨hn, by rw [ite_eq_left ht]; exact hv, trivial⟩, hb, hp, htot, hl, fun _ => hd, fun _ => hq⟩
  · obtain ⟨k, hkv, hkb, hkp, hkt, hkl, -⟩ := kidB_ofIn (P := coreProgram) (fs := fs) (cert := cert)
      (rd := rd) (σ := σ) (b := b) (m := m) (Rk := Rk) (Dk := Dk) hc
      (show (if c.taken then RelAtInB S coreProgram fs cert rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ)
        else m = fs c.f) by rw [ite_eq_right ht] at h ⊢; exact h)
    exact ⟨k, hkv, hkb, hkp, hkt, hkl, fun h' => absurd h' ht, fun h' => absurd h' ht⟩

/-- **`relAtInB_of_walk_loop` with predicates.** -/
theorem relAtInBT_of_walk_loop {R D Dk Rt Dt : ℕ → Prop} {fp m N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {cs : List Call} {c : Call}
    {Qt Q : Tree → Prop}
    (hf : coreProgram.find? f = some fn) (hl : coreProgram.loop f = true) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.HoldsB S rd σ)
    (hc : calls es = cs ++ [c])
    (htail : if c.taken then RelAtInBT S fs cert rd Rt Dt (fp + fs f) m c.f (c.args.map σ) (c.rets.map σ) Qt
      else m = fs c.f)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f + m) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromInB S coreProgram fs cert rd σ (fun i => R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i)
      (fun _ => False) cs (fp + fs f + m + (allocs σ es).sum) N Dk)
    (hRt : ∀ i, Rt i → R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ R i ∨ Dk i ∨ (c.taken = true ∧ Dt i)))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i ∨
      (c.taken = true ∧ Dt i))
    (hQ : ∀ (ks : List Tree) (k : Tree), Tree.KidsValidB S coreProgram rd σ cs ks →
      Tree.KidsValidB S coreProgram rd σ [c] [k] → (c.taken = true → Qt k) →
      Q (Memory.Tree.node f σ (allocs σ es) (ks ++ [k]))) :
    RelAtInBT S fs cert rd R D fp (fs f + m + (allocs σ es).sum + N) f args rets Q := by
  have htk := takes_of_calls coreProgram_wf (List.mem_of_find?_eq_some hf) hw
  rw [hc] at htk
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl⟩ := kidsB_of_kidsFromIn _ _ _ _ _ _
    (fun c' hc' => htk c' (List.mem_append_left _ hc')) hk
  obtain ⟨k, hkv', hkb', hkp', hkt, hkl', hkd', hkq⟩ :=
    kidBT_ofIn (htk c (List.mem_append_right _ List.mem_cons_self)) htail
  have hns : (ks ++ [k]).map (Tree.total fs) = ks.map (Tree.total fs) ++ [m] := by
    rw [List.map_append, List.map_singleton, hkt]
  have hbb : bufBase fs coreProgram.loop fp f ((ks ++ [k]).map (Tree.total fs)) = fp + fs f + m := by
    rw [hns]; simp [bufBase, hl]
  have hkpos : kidPos fs coreProgram.loop fp f (allocs σ es) ((ks ++ [k]).map (Tree.total fs)) =
      bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs)) ++ [fp + fs f] := by
    rw [kidPos, ite_eq_left hl, hbb, hns, List.dropLast_concat, List.getLast?_concat]
    rfl
  have hlen : (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))).length = ks.length := by
    rw [length_bases, List.length_map]
  have hdata : ∀ i, (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i ↔
      ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨
        Tree.DataKids coreProgram fs cert (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))) ks i ∨
        k.Data coreProgram fs cert (fp + fs f) i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos, dataKids_append hlen, dataKids_cons]
    simp only [not_dataKids_nil, or_false]
  refine ⟨.node f σ (allocs σ es) (ks ++ [k]), hQ ks k hkv hkv' hkq, rfl,
    ⟨fn, hf, hp, es, vs, hw, hr, hes, by rw [hc]; exact kidsValidB_append hkv hkv'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Tree.BufsOk, events_node hf hw]
    refine ⟨rfl, bufsOkKids_append hkb ?_⟩
    rw [Tree.BufsOkKids, Tree.BufsOkKids]
    exact ⟨hkb', trivial⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    refine ⟨⟨hbuf, haddr⟩, placedKids_append hlen hkp ?_⟩
    rw [placedKids_cons]
    exact ⟨hkp', placedKids_nil⟩
  · rw [total_node, totalKids_eq_sum, hns, List.sum_append, hks]
    simp only [List.sum_cons, List.sum_nil]
    omega
  · have hDk : ∀ i, Dk i → (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i :=
      fun i h => (hkd i h).elim (fun h => h.elim) fun h => (hdata i).mpr (Or.inr (Or.inl h))
    have hDt : ∀ i, c.taken = true ∧ Dt i → (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i :=
      fun i h => (hdata i).mpr (Or.inr (Or.inr (hkd' h.1 i h.2)))
    have hown : ∀ i, ownData cert fp (fp + fs f + m) f (allocs σ es) es i →
        (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i :=
      fun i h => (hdata i).mpr (Or.inl h)
    rw [loadsIn_node, events_node hf hw, hkpos]
    refine ⟨fun A hA => ?_, loadsInKids_append hlen ?_ ?_⟩
    · obtain ⟨i, hi, h⟩ := hload A hA
      refine ⟨i, hi, ?_⟩
      rcases h with h | h | h | h
      · exact Or.inl (hown i h)
      · exact Or.inr h
      · exact Or.inl (hDk i h)
      · exact Or.inl (hDt i h)
    · exact hkl _ (fun i hi => hi.elim Or.inr fun h => Or.inl (hown i h)) (fun _ h => h.elim)
        (fun i hi => Or.inl ((hdata i).mpr (Or.inr (Or.inl hi))))
    · rw [loadsInKids_cons]
      refine ⟨loadsIn_mono k _ (fun i hi => ?_) hkl', loadsInKids_nil⟩
      rcases hRt i hi with h | h | h
      · exact Or.inr h
      · exact Or.inl (hown i h)
      · exact Or.inl (hDk i h)
  · intro i hi
    rcases hD i hi with h | h | h
    · exact (hdata i).mpr (Or.inl h)
    · exact (hkd i h).elim (fun h => h.elim) fun h => (hdata i).mpr (Or.inr (Or.inl h))
    · exact (hdata i).mpr (Or.inr (Or.inr (hkd' h.1 i h.2)))

/-! ## Without weights -/

/-- No weights: the trees' predicates of `TreeRoot.lean`'s weighted forms at `Θ := Empty`. -/
abbrev wE : Empty → String → ℕ := fun e => e.elim

/-- No weight bounds. -/
abbrev bwE : Empty → ℕ := fun e => e.elim

theorem RelAtInBT.dmono {R D D' : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E} {Q : Tree → Prop}
    (h : RelAtInBT S fs cert rd R D fp n f args rets Q) (hD : ∀ i, D' i → D i) :
    RelAtInBT S fs cert rd R D' fp n f args rets Q :=
  let ⟨t, hq, h1, h2, h3, h4, h5, h6, h7⟩ := h
  ⟨t, hq, h1, h2, h3, h4, h5, h6, fun i hi => h7 i (hD i hi)⟩

theorem RelAtInWST.toBT {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E} {Bw : Empty → ℕ}
    {Q : Tree → Prop} (h : RelAtInWST S fs cert wE rd R D fp n f args rets Bw Q) :
    RelAtInBT S fs cert rd R D fp n f args rets Q :=
  let ⟨t, hq, h1, h2, h3, h4, h5, h6, h7, _⟩ := h
  ⟨t, hq, h1, h2, h3, h4, h5, h6, h7⟩

theorem CompleteAtBST.toWSTE {κ : ℕ} {f : String} {Lin : Main.Layout} {args : List E}
    {Out : List E → Main.Layout → Prop} {B : ℕ} {Q : ℕ → Reader → Tree → Prop}
    (h : CompleteAtBST S fs cert κ f Lin args Out B Q) : CompleteAtWST S fs cert wE κ f Lin args Out B bwE Q :=
  fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hq, hn', hv, hb, hp, ht, hl', hd'⟩ := hr rd hl hm
    ⟨t, hq, hn', hv, hb, hp, ht, hl', hd', fun θ => θ.elim⟩⟩

theorem CompleteAtBST.monoT {κ κ' : ℕ} {f : String} {Lin : Main.Layout} {args : List E}
    {Out : List E → Main.Layout → Prop} {B B' : ℕ} {Q Q' : ℕ → Reader → Tree → Prop}
    (h : CompleteAtBST S fs cert κ' f Lin args Out B Q) (hk : κ' ≤ κ) (hB : B ≤ B')
    (hQ : ∀ fp rd t, Q fp rd t → Q' fp rd t) : CompleteAtBST S fs cert κ f Lin args Out B' Q' := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, le_trans hn hB, fun rd hl hm =>
    let ⟨t, hq, hn', hv, hb, hp, ht, hl', hd'⟩ := hr rd (hl.mono hk) hm
    ⟨t, hQ fp rd t hq, hn', hv, hb, hp, ht, hl', hd'⟩⟩

end
end LeanVM.Guest.B1
