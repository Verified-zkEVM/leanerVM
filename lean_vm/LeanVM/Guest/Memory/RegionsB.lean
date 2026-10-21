/-
  LeanVM.Guest.Memory.RegionsB

  Placed relations loading from a region (`Regions.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.Regions
public import LeanVM.Guest.Memory.PlacedB

/-!
# Regions under any `BLAKE2S` semantics

`Regions.lean`'s `RelAtIn`, `KidsFromIn` and `Program.RelIn`, with `S : BlakeSem` a parameter
(`RelAtInB`, `KidsFromInB`, `Program.RelInB`), and the lemmas about them: `relAtInB_of_walk`,
`relAtInB_of_walk_loop`, `relInB_of_walk`, `loadsRB_of_quiet`, `relAtInB_of_rel_quiet`, ….

* `relAtInB_deployed`, `kidsFromInB_deployed`, `relInB_deployed`: at `blakeDeployed`, they are
  `Regions.lean`'s.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

/-! ## Runs and loads of a path -/

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ)

variable (S) in
/-- **`Program.RelB` placed at `fp`, loading from `R`**: `RelAtB` by a tree whose loads read its
data or `R`, and whose data contains `D`. -/
def RelAtInB (rd : Reader) (R D : ℕ → Prop) (fp n : ℕ) (f : String) (args rets : List E) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.ValidB S P rd args rets ∧ t.BufsOk P ∧ t.Placed P fs cert fp ∧
    t.total fs = n ∧ t.LoadsIn P fs cert R fp ∧ ∀ i, D i → t.Data P fs cert fp i

variable (S) in
/-- **The callees of the frames `cs` sets up**, as `KidsFromB`, each loading from a region within
`R` and the data `Dacc` earlier callees claimed, claiming data `Dk` for the later ones; `Dend`
within all claimed. -/
def KidsFromInB (rd : Reader) (σ : Val) (R : ℕ → Prop) :
    (ℕ → Prop) → List Call → ℕ → ℕ → (ℕ → Prop) → Prop
  | Dacc, [], _, n, Dend => n = 0 ∧ ∀ i, Dend i → Dacc i
  | Dacc, c :: cs, b, n, Dend => ∃ (m n' : ℕ) (Rk Dk : ℕ → Prop), n = m + n' ∧
      (∀ i, Rk i → R i ∨ Dacc i) ∧
      (if c.taken then RelAtInB S P fs cert rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ)
        else m = fs c.f) ∧
      KidsFromInB rd σ R (fun i => Dacc i ∨ (c.taken = true ∧ Dk i)) cs (b + m) n' Dend

variable {P fs cert}

theorem RelAtInB.relAt {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtInB S P fs cert rd R D fp n f args rets) : RelAtB S P fs cert rd fp n f args rets :=
  let ⟨t, hn, hv, hb, hp, ht, _⟩ := h
  ⟨t, hn, hv, hb, hp, ht⟩

/-! ## Composition -/

section Compose

variable {rd : Reader} {σ : Val}

/-- The callee of one frame, its loads in its region and its data containing its claim. -/
theorem kidB_ofIn {c : Call} {b m : ℕ} {Rk Dk : ℕ → Prop}
    (hc : c.taken = false → P.Takes c.f c.args.length = true)
    (h : if c.taken then RelAtInB S P fs cert rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ)
      else m = fs c.f) :
    ∃ k : Tree, Tree.KidsValidB S P rd σ [c] [k] ∧ k.BufsOk P ∧ k.Placed P fs cert b ∧
      k.total fs = m ∧ k.LoadsIn P fs cert Rk b ∧ (c.taken = true → ∀ i, Dk i → k.Data P fs cert b i) := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at h
    obtain ⟨k, hn, hv, hb, hp, htot, hl, hd⟩ := h
    exact ⟨k, ⟨hn, by rw [ite_eq_left ht]; exact hv, trivial⟩, hb, hp, htot, hl, fun _ => hd⟩
  · rw [ite_eq_right ht] at h
    obtain ⟨k, hkv, hkb, hkp, hkt⟩ := kidB_of (P := P) (fs := fs) (cert := cert) (rd := rd)
      (σ := σ) (b := b) (m := m) hc (by rw [ite_eq_right ht]; exact h)
    have hk := hkv.2.1
    rw [ite_eq_right ht] at hk
    obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
    exact ⟨_, hkv, hkb, hkp, hkt, loadsIn_phantom, fun h' => absurd h' ht⟩

/-- The callees of `KidsFromInB`, placed one after another from `b`. -/
theorem kidsB_of_kidsFromIn (R : ℕ → Prop) : ∀ (cs : List Call) (Dacc : ℕ → Prop) (b n : ℕ)
    (Dend : ℕ → Prop), (∀ c ∈ cs, c.taken = false → P.Takes c.f c.args.length = true) →
    KidsFromInB S P fs cert rd σ R Dacc cs b n Dend →
    ∃ ks : List Tree, Tree.KidsValidB S P rd σ cs ks ∧ Tree.BufsOkKids P ks ∧
      Tree.PlacedKids P fs cert (bases b (ks.map (Tree.total fs))) ks ∧
      (ks.map (Tree.total fs)).sum = n ∧
      (∀ i, Dend i → Dacc i ∨ Tree.DataKids P fs cert (bases b (ks.map (Tree.total fs))) ks i) ∧
      ∀ Rp : ℕ → Prop, (∀ i, R i → Rp i) → (∀ i, Dacc i → Rp i) →
        (∀ i, Tree.DataKids P fs cert (bases b (ks.map (Tree.total fs))) ks i → Rp i) →
        Tree.LoadsInKids P fs cert Rp (bases b (ks.map (Tree.total fs))) ks
  | [], Dacc, _, n, Dend, _, h => by
      rw [KidsFromInB] at h
      refine ⟨[], by simp [Tree.KidsValidB], by rw [Tree.BufsOkKids]; trivial, placedKids_nil,
        by simp [h.1], fun i hi => Or.inl (h.2 i hi), fun _ _ _ _ => loadsInKids_nil⟩
  | c :: cs, Dacc, b, n, Dend, hw, h => by
      rw [KidsFromInB] at h
      obtain ⟨m, n', Rk, Dk, rfl, hRk, hc, hcs⟩ := h
      obtain ⟨k, hkv, hkb, hkp, hkt, hkl, hkd⟩ := kidB_ofIn (hw c List.mem_cons_self) hc
      obtain ⟨ks, hv, hb, hp, hs, hd, hl⟩ := kidsB_of_kidsFromIn R cs _ (b + m) n' Dend
        (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) hcs
      have hpos : bases b ((k :: ks).map (Tree.total fs)) = b :: bases (b + m) (ks.map (Tree.total fs)) := by
        rw [List.map_cons, bases, hkt]
      refine ⟨k :: ks, ⟨hkv.1, hkv.2.1, hv⟩, by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, ?_, ?_, ?_, ?_⟩
      · rw [hpos, placedKids_cons]; exact ⟨hkp, hp⟩
      · rw [List.map_cons, List.sum_cons, hkt, hs]
      · intro i hi
        rw [hpos, dataKids_cons]
        rcases hd i hi with (h | ⟨ht, h⟩) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (hkd ht i h))
        · exact Or.inr (Or.inr h)
      · intro Rp hR hD hK
        rw [hpos] at hK ⊢
        rw [loadsInKids_cons]
        refine ⟨loadsIn_mono k b (fun i hi => (hRk i hi).elim (hR i) (hD i)) hkl,
          hl Rp hR (fun i hi => ?_) (fun i hi => hK i (dataKids_cons.mpr (Or.inr hi)))⟩
        rcases hi with h | ⟨ht, h⟩
        · exact hD i h
        · exact hK i (dataKids_cons.mpr (Or.inl (hkd ht i h)))

/-- **Composition with regions**, a function that is not a loop helper (or whose path calls
nothing): as `relAtB_of_walk`, its callees in `KidsFromInB` from its region and its own data, its
loads in its own data, its region or its callees' claims, and its claim within its own data and
its callees' claims. -/
theorem relAtInB_of_walk (hP : P.Wf) {R D Dk : ℕ → Prop} {fp N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} (hf : P.find? f = some fn)
    (hl : P.loop f = false ∨ calls es = []) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.HoldsB S rd σ)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromInB S P fs cert rd σ (fun i => R i ∨ ownData cert fp (fp + fs f) f (allocs σ es) es i)
      (fun _ => False) (calls es) (fp + fs f + (allocs σ es).sum) N Dk)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ R i ∨ Dk i))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ Dk i) :
    RelAtInB S P fs cert rd R D fp (fs f + (allocs σ es).sum + N) f args rets := by
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl⟩ :=
    kidsB_of_kidsFromIn _ _ _ _ _ _ (takes_of_calls hP (List.mem_of_find?_eq_some hf) hw) hk
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
  refine ⟨.node f σ (allocs σ es) ks, rfl, ⟨fn, hf, hp, es, vs, hw, hr, hes, hkv⟩, ?_, ?_, ?_, ?_, ?_⟩
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

/-- **Composition with regions**, a loop helper: as `relAtB_of_walk_loop`, its tail call loading
from its region, its own data and its other callees' claims, and claiming `Dt`. -/
theorem relAtInB_of_walk_loop (hP : P.Wf) {R D Dk Rt Dt : ℕ → Prop} {fp m N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {cs : List Call} {c : Call}
    (hf : P.find? f = some fn) (hl : P.loop f = true) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.HoldsB S rd σ)
    (hc : calls es = cs ++ [c])
    (htail : if c.taken then RelAtInB S P fs cert rd Rt Dt (fp + fs f) m c.f (c.args.map σ) (c.rets.map σ)
      else m = fs c.f)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f + m) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromInB S P fs cert rd σ (fun i => R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i)
      (fun _ => False) cs (fp + fs f + m + (allocs σ es).sum) N Dk)
    (hRt : ∀ i, Rt i → R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ R i ∨ Dk i ∨ (c.taken = true ∧ Dt i)))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i ∨
      (c.taken = true ∧ Dt i)) :
    RelAtInB S P fs cert rd R D fp (fs f + m + (allocs σ es).sum + N) f args rets := by
  have htk := takes_of_calls hP (List.mem_of_find?_eq_some hf) hw
  rw [hc] at htk
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl⟩ := kidsB_of_kidsFromIn _ _ _ _ _ _
    (fun c' hc' => htk c' (List.mem_append_left _ hc')) hk
  obtain ⟨k, hkv', hkb', hkp', hkt, hkl', hkd'⟩ :=
    kidB_ofIn (htk c (List.mem_append_right _ List.mem_cons_self)) htail
  have hns : (ks ++ [k]).map (Tree.total fs) = ks.map (Tree.total fs) ++ [m] := by
    rw [List.map_append, List.map_singleton, hkt]
  have hbb : bufBase fs P.loop fp f ((ks ++ [k]).map (Tree.total fs)) = fp + fs f + m := by
    rw [hns]; simp [bufBase, hl]
  have hkpos : kidPos fs P.loop fp f (allocs σ es) ((ks ++ [k]).map (Tree.total fs)) =
      bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs)) ++ [fp + fs f] := by
    rw [kidPos, ite_eq_left hl, hbb, hns, List.dropLast_concat, List.getLast?_concat]
    rfl
  have hlen : (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))).length = ks.length := by
    rw [length_bases, List.length_map]
  have hdata : ∀ i, (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i ↔
      ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨
        Tree.DataKids P fs cert (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))) ks i ∨
        k.Data P fs cert (fp + fs f) i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos, dataKids_append hlen, dataKids_cons]
    simp only [not_dataKids_nil, or_false]
  refine ⟨.node f σ (allocs σ es) (ks ++ [k]), rfl,
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
  · have hDk : ∀ i, Dk i → (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i := fun i h =>
      (hkd i h).elim (fun h => h.elim) fun h => (hdata i).mpr (Or.inr (Or.inl h))
    have hDt : ∀ i, c.taken = true ∧ Dt i → (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i :=
      fun i h => (hdata i).mpr (Or.inr (Or.inr (hkd' h.1 i h.2)))
    have hown : ∀ i, ownData cert fp (fp + fs f + m) f (allocs σ es) es i →
        (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i := fun i h => (hdata i).mpr (Or.inl h)
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

end Compose

/-! ## Loads by region only -/

section Pure

variable {Sz : List String}

variable (S) in
/-- **`Program.RelB` loading from `R` only**, by a tree whose `HeapBuf`s are its paths'. -/
def _root_.LeanVM.Guest.Core.Program.RelInB (P : Core.Program) (rd : Reader) (R : ℕ → Prop)
    (f : String) (args rets : List E) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.ValidB S P rd args rets ∧ t.BufsOk P ∧ t.LoadsR P R

theorem _root_.LeanVM.Guest.Core.Program.RelInB.rel {rd : Reader} {R : ℕ → Prop} {f : String} {args rets : List E}
    (h : P.RelInB S rd R f args rets) : P.RelB S rd f args rets :=
  let ⟨t, hn, hv, _⟩ := h
  hn ▸ hv.rel t

/-- **A function of a pure set loading from `R` is placed anywhere**, loading from `R`. -/
theorem relAtInB_of_relIn_pure (hS : P.PureIn Sz) {rd : Reader} {R : ℕ → Prop} {g : String}
    (hg : g ∈ Sz) {args rets : List E} (h : P.RelInB S rd R g args rets) :
    ∃ n, ∀ fp, RelAtInB S P fs cert rd R (fun _ => False) fp n g args rets := by
  obtain ⟨t, hn, hv, hb, hl⟩ := h
  exact ⟨t.total fs, fun fp => ⟨t, hn, hv, hb, placedB_of_pure hS t hv hb (hn ▸ hg) fp, rfl,
    loadsIn_of_loadsR t R fp hl, fun _ h => h.elim⟩⟩

variable {rd : Reader} {σ : Val}

/-- The callees of the frames `cs`: each call entered `RelIn R`, each not a phantom. -/
theorem kidsB_of_relIn {R : ℕ → Prop} : ∀ cs : List Call,
    (∀ c ∈ cs, c.taken = false → P.Takes c.f c.args.length = true) →
    (∀ c ∈ cs, c.taken = true → P.RelInB S rd R c.f (c.args.map σ) (c.rets.map σ)) →
    ∃ ks, Tree.KidsValidB S P rd σ cs ks ∧ Tree.BufsOkKids P ks ∧ Tree.LoadsRKids P R ks
  | [], _, _ => ⟨[], by simp [Tree.KidsValidB], by rw [Tree.BufsOkKids]; trivial,
      by rw [Tree.LoadsRKids]; trivial⟩
  | c :: cs, hw, hc => by
      obtain ⟨ks, hv, hb, hl⟩ := kidsB_of_relIn cs (fun c' h => hw c' (List.mem_cons_of_mem _ h))
        (fun c' h => hc c' (List.mem_cons_of_mem _ h))
      by_cases ht : c.taken = true
      · obtain ⟨k, hn, hkv, hkb, hkl⟩ := hc c List.mem_cons_self ht
        refine ⟨k :: ks, ⟨hn, by rw [ite_eq_left ht]; exact hkv, hv⟩,
          by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, by rw [Tree.LoadsRKids]; exact ⟨hkl, hl⟩⟩
      · obtain ⟨σ', hph⟩ := phantom_of_takes (P := P) (f := c.f) (ws := c.args.map σ)
          (by rw [List.length_map]; exact hw c List.mem_cons_self (by simpa using ht))
        refine ⟨.phantom c.f σ' :: ks, ⟨rfl, by rw [ite_eq_right ht]; exact ⟨⟨_, _, rfl⟩, hph⟩, hv⟩,
          by rw [Tree.BufsOkKids, Tree.BufsOk]; exact ⟨trivial, hb⟩,
          by rw [Tree.LoadsRKids, Tree.LoadsR]; exact ⟨trivial, hl⟩⟩

/-- **`RelIn` along a path**: the parameters, the path, its loads in `R`, and every call entered
`RelIn R`. -/
theorem relInB_of_walk (hP : P.Wf) {R : ℕ → Prop} {f : String} {args rets : List E} {fn : Fn}
    {es : List Ev} {vs : List V} (hf : P.find? f = some fn) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.HoldsB S rd σ)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ R i)
    (hk : ∀ c ∈ calls es, c.taken = true → P.RelInB S rd R c.f (c.args.map σ) (c.rets.map σ)) :
    P.RelInB S rd R f args rets := by
  obtain ⟨ks, hkv, hkb, hkl⟩ := kidsB_of_relIn (calls es)
    (takes_of_calls hP (List.mem_of_find?_eq_some hf) hw) hk
  refine ⟨.node f σ (allocs σ es) ks, rfl, ⟨fn, hf, hp, es, vs, hw, hr, hes, hkv⟩, ?_, ?_⟩
  · rw [Tree.BufsOk, events_node hf hw]
    exact ⟨rfl, hkb⟩
  · rw [Tree.LoadsR, events_node hf hw]
    exact ⟨hload, hkl⟩

/-! ### Subtrees without loads -/

mutual
/-- A valid tree of a function of a quiet set loads nothing. -/
theorem loadsRB_of_quiet (hS : P.QuietIn Sz) (R : ℕ → Prop) : ∀ (t : Tree) {args rets : List E},
    t.ValidB S P rd args rets → t.name ∈ Sz → t.LoadsR P R
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hn => by
      have hq : ∀ e ∈ es, e.quiet := by
        have := walk_quiet (σ := σ) fn.body (hS f hn fn hf)
        rwa [hw] at this
      rw [Tree.LoadsR, events_node hf hw, loadAddrs_quiet hq]
      refine ⟨fun _ h => (List.not_mem_nil h).elim, loadsRKidsB_of_quiet hS R kids σ (calls es) hk ?_⟩
      exact calls_pure fun e he => by
        have := hq e he
        have hp := walk_pure (σ := σ) fn.body (quietList_pure fn.body (hS f hn fn hf))
        rw [hw] at hp
        exact hp e he
  | .phantom .., _, _, h, _ => h.elim

/-- `loadsRB_of_quiet` for the callees. -/
theorem loadsRKidsB_of_quiet (hS : P.QuietIn Sz) (R : ℕ → Prop) : ∀ (ks : List Tree) (σ : Val)
    (cs : List Call), Tree.KidsValidB S P rd σ cs ks → (∀ c ∈ cs, c.f ∈ Sz) → Tree.LoadsRKids P R ks
  | [], _, _, _, _ => by rw [Tree.LoadsRKids]; trivial
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hS' => by
      rw [Tree.LoadsRKids]
      refine ⟨?_, loadsRKidsB_of_quiet hS R ks σ cs hks fun c' h => hS' c' (List.mem_cons_of_mem _ h)⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact loadsRB_of_quiet hS R k hc (hn ▸ hS' c List.mem_cons_self)
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        rw [Tree.LoadsR]; trivial
  | _ :: _, _, [], h, _ => h.elim
end

/-- **A function of a quiet set is placed anywhere, loading nothing**: `Program.RelB` gives
`RelAtInB` at every frame pointer and region, of one size. -/
theorem relAtInB_of_rel_quiet (hP : P.Wf) (hS : P.QuietIn Sz) {g : String} (hg : g ∈ Sz)
    {args rets : List E} (h : P.RelB S rd g args rets) :
    ∃ n, ∀ fp R, RelAtInB S P fs cert rd R (fun _ => False) fp n g args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.RelB.tree hP h
  exact ⟨t.total fs, fun fp R => ⟨t, hn, hv, hb, placedB_of_pure hS.pureIn t hv hb (hn ▸ hg) fp, rfl,
    loadsIn_of_loadsR t R fp (loadsRB_of_quiet hS R t hv (hn ▸ hg)), fun _ h => h.elim⟩⟩

end Pure

/-! ## At the deployed semantics -/

section Deployed

variable {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader}

/-- At the deployed semantics, `RelAtInB` is `Regions.lean`'s `RelAtIn`. -/
theorem relAtInB_deployed (R D : ℕ → Prop) (fp n : ℕ) (f : String) (args rets : List E) :
    RelAtInB blakeDeployed P fs cert rd R D fp n f args rets =
      RelAtIn P fs cert rd R D fp n f args rets := by
  simp only [RelAtInB, RelAtIn, validB_deployed]

/-- At the deployed semantics, `KidsFromInB` is `Regions.lean`'s `KidsFromIn`. -/
theorem kidsFromInB_deployed (σ : Val) (R : ℕ → Prop) : ∀ (Dacc : ℕ → Prop) (cs : List Call)
    (b n : ℕ) (Dend : ℕ → Prop),
    KidsFromInB blakeDeployed P fs cert rd σ R Dacc cs b n Dend =
      KidsFromIn P fs cert rd σ R Dacc cs b n Dend
  | _, [], _, _, _ => by simp only [KidsFromInB, KidsFromIn]
  | Dacc, c :: cs, b, n, Dend => by
      simp only [KidsFromInB, KidsFromIn, relAtInB_deployed, kidsFromInB_deployed σ R _ cs]

/-- At the deployed semantics, `Program.RelInB` is `Regions.lean`'s `Program.RelIn`. -/
theorem relInB_deployed (R : ℕ → Prop) (f : String) (args rets : List E) :
    P.RelInB blakeDeployed rd R f args rets = P.RelIn rd R f args rets := by
  simp only [Program.RelInB, Program.RelIn, validB_deployed]

end Deployed

end
end LeanVM.Guest.Memory
