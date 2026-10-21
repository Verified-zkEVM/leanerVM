/-
  LeanVM.Guest.B1.Comp.TreeRoot

  The uniform placed form within weights under any semantics, its tree satisfying a predicate,
  the callees' predicates carried up to their caller.
-/

module

public import LeanVM.Guest.B1.Main.WeightBS

/-!
# Placed trees with a property, composed

`Main.CompleteAtWS` (`WeightAtS.lean`) says some placed tree exists; what it holds (its node's
valuation, the frames below it) is forgotten. Here the same forms keep a predicate `Q` of the tree:

* `RelAtInWST`, `CompleteAtWST` (`RelAtInWS`, `CompleteAtWS` by a tree satisfying `Q`, which may
  depend on the frame pointer and the memory), and the bounded `RelAtInBT`, `CompleteAtBST`;
* `KidsFromInWST` (`KidsFromInWS`, each entered callee's tree satisfying its predicate at its
  frame pointer) and `KidsSat` (each entered callee's tree, at the position it is placed, satisfies
  its predicate);
* `kidsFromInWST_of_kidsBW`: callees `CompleteAtWST` with predicates give `KidsFromInWST`
  (`kidsFromInWS_of_kidsBW`);
* `relAtInWST_of_walk`: a caller's node whose callees' trees satisfy `KidsSat` satisfies any
  predicate `Q` of the node they give (`relAtInWS_of_walk`).

`True` predicates give back the forms without one (`CompleteAtWST.toWS`, `CompleteAtWS.toWST`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append kidsWs kidsWs_sum kidsBoundW)

@[expose] public section

section Defs

variable (S : BlakeSem) (fs : String → ℕ) (cert : String → V → ℕ) {Θ : Type} (w : Θ → String → ℕ)

/-- **`RelAtInWS` by a tree satisfying `Q`.** -/
def RelAtInWST (rd : Reader) (R D : ℕ → Prop) (fp n : ℕ) (f : String) (args rets : List E)
    (Bw : Θ → ℕ) (Q : Tree → Prop) : Prop :=
  ∃ t : Tree, Q t ∧ t.name = f ∧ t.ValidB S coreProgram rd args rets ∧ t.BufsOk coreProgram ∧
    t.Placed coreProgram fs cert fp ∧ t.total fs = n ∧ t.LoadsIn coreProgram fs cert R fp ∧
    (∀ i, D i → t.Data coreProgram fs cert fp i) ∧ ∀ θ, t.weight (w θ) ≤ Bw θ

/-- **`RelAtInB` by a tree satisfying `Q`.** -/
def RelAtInBT (rd : Reader) (R D : ℕ → Prop) (fp n : ℕ) (f : String) (args rets : List E)
    (Q : Tree → Prop) : Prop :=
  ∃ t : Tree, Q t ∧ t.name = f ∧ t.ValidB S coreProgram rd args rets ∧ t.BufsOk coreProgram ∧
    t.Placed coreProgram fs cert fp ∧ t.total fs = n ∧ t.LoadsIn coreProgram fs cert R fp ∧
    ∀ i, D i → t.Data coreProgram fs cert fp i

/-- **`CompleteAtWS` by trees satisfying `Q fp rd`** at the frame pointer `fp` on the memory `rd`. -/
def CompleteAtWST (κ : ℕ) (f : String) (Lin : Layout) (args : List E)
    (Out : List E → Layout → Prop) (B : ℕ) (Bw : Θ → ℕ) (Q : ℕ → Reader → Tree → Prop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ n ≤ B ∧ ∀ rd, LowDef κ rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInWST S fs cert w rd (RegionL Lin) (RegionL Lout) fp n f args rets Bw (Q fp rd)

/-- **`CompleteAtBS` by trees satisfying `Q fp rd`.** -/
def CompleteAtBST (κ : ℕ) (f : String) (Lin : Layout) (args : List E)
    (Out : List E → Layout → Prop) (B : ℕ) (Q : ℕ → Reader → Tree → Prop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ n ≤ B ∧ ∀ rd, LowDef κ rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInBT S fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets (Q fp rd)

/-- **`KidsFromInWS` with predicates**: each entered callee's tree satisfies its predicate at its
frame pointer. -/
def KidsFromInWST (rd : Reader) (σ : Val) (R : ℕ → Prop) :
    (ℕ → Prop) → List Call → List (Θ → ℕ) → List (ℕ → Tree → Prop) → ℕ → ℕ → (ℕ → Prop) → Prop
  | Dacc, [], _, _, _, n, Dend => n = 0 ∧ ∀ i, Dend i → Dacc i
  | _, _ :: _, [], _, _, _, _ => False
  | _, _ :: _, _ :: _, [], _, _, _ => False
  | Dacc, c :: cs, bw :: bws, q :: qs, b, n, Dend => ∃ (m n' : ℕ) (Rk Dk : ℕ → Prop), n = m + n' ∧
      (∀ i, Rk i → R i ∨ Dacc i) ∧
      (if c.taken then RelAtInWST S fs cert w rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ) bw (q b)
        else m = fs c.f) ∧
      KidsFromInWST rd σ R (fun i => Dacc i ∨ (c.taken = true ∧ Dk i)) cs bws qs (b + m) n' Dend

/-- **Callees within bounds and weights, with predicates** (`KidsWS`). -/
def KidsWST (κ : ℕ) : List Kid → List ℕ → List (Θ → ℕ) → List (ℕ → Reader → Tree → Prop) → Prop
  | k :: ks, B :: bs, Bw :: bws, Q :: Qs =>
      (k.taken = true → CompleteAtWST S fs cert w κ k.f k.Lin k.args k.Out B Bw Q) ∧
      (k.taken = false → fs k.f ≤ B) ∧ KidsWST κ ks bs bws Qs
  | [], [], [], [] => True
  | _, _, _, _ => False

end Defs

/-- **Each entered callee's tree, at the position it is placed, satisfies its predicate.** -/
def KidsSat : List Call → List (ℕ → Tree → Prop) → List ℕ → List Tree → Prop
  | c :: cs, q :: qs, b :: bs, k :: ks => (c.taken = true → q b k) ∧ KidsSat cs qs bs ks
  | _, _, _, _ => True

variable {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ}

/-! ## Forgetting and adding predicates -/

theorem RelAtInWST.toWS {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Bw : Θ → ℕ} {Q : Tree → Prop} (h : RelAtInWST S fs cert w rd R D fp n f args rets Bw Q) :
    Main.RelAtInWS S fs cert w rd R D fp n f args rets Bw :=
  let ⟨t, _, hn, hv, hb, hp, ht, hl, hd, hw⟩ := h
  ⟨t, hn, hv, hb, hp, ht, hl, hd, hw⟩

theorem CompleteAtWST.toWS {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ} {Q : ℕ → Reader → Tree → Prop}
    (h : CompleteAtWST S fs cert w κ f Lin args Out B Bw Q) :
    Main.CompleteAtWS S fs cert w κ f Lin args Out B Bw := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm => (hr rd hl hm).toWS⟩

theorem CompleteAtWS.toWST {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ}
    (h : Main.CompleteAtWS S fs cert w κ f Lin args Out B Bw) :
    CompleteAtWST S fs cert w κ f Lin args Out B Bw fun _ _ _ => True := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hn', hv, hb, hp, ht, hl', hd', hw⟩ := hr rd hl hm
    ⟨t, trivial, hn', hv, hb, hp, ht, hl', hd', hw⟩⟩

theorem CompleteAtBS.toBST {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} (h : CompleteAtBS S fs cert κ f Lin args Out B) :
    CompleteAtBST S fs cert κ f Lin args Out B fun _ _ _ => True := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hn', hv, hb, hp, ht, hl', hd'⟩ := hr rd hl hm
    ⟨t, trivial, hn', hv, hb, hp, ht, hl', hd'⟩⟩

theorem CompleteAtBST.toBS {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Q : ℕ → Reader → Tree → Prop}
    (h : CompleteAtBST S fs cert κ f Lin args Out B Q) : CompleteAtBS S fs cert κ f Lin args Out B :=
  fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, _, hn', hv, hb, hp, ht, hl', hd'⟩ := hr rd hl hm
    ⟨t, hn', hv, hb, hp, ht, hl', hd'⟩⟩

/-- `CompleteAtB.toWS_weightLe` with predicates. -/
theorem CompleteAtBST.toWST_weightLe {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bf : Θ → List E → ℕ} {Q : ℕ → Reader → Tree → Prop}
    (h : CompleteAtBST S fs cert κ f Lin args Out B Q)
    (hw : ∀ θ, WeightLeB S coreProgram (w θ) f (Bf θ)) :
    CompleteAtWST S fs cert w κ f Lin args Out B (fun θ => Bf θ args) Q := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hq, hn', hv, hb, hp, ht, hl', hd'⟩ := hr rd hl hm
    ⟨t, hq, hn', hv, hb, hp, ht, hl', hd', fun θ => hw θ rd t args _ hn' hv hb⟩⟩

theorem CompleteAtWST.wmono {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw Bw' : Θ → ℕ} {Q : ℕ → Reader → Tree → Prop}
    (h : CompleteAtWST S fs cert w κ f Lin args Out B Bw Q) (hB : ∀ θ, Bw θ ≤ Bw' θ) :
    CompleteAtWST S fs cert w κ f Lin args Out B Bw' Q := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hq, hn', hv, hb, hp, ht, hl', hd', hw⟩ := hr rd hl hm
    ⟨t, hq, hn', hv, hb, hp, ht, hl', hd', fun θ => (hw θ).trans (hB θ)⟩⟩

/-! ## The callees -/

section Compose

variable {rd : Reader} {σ : Val}

/-- The callee of one frame, its tree satisfying `q b` when entered (`kidS_ofInW`). -/
theorem kidST_ofInW {c : Call} {b m : ℕ} {Rk Dk : ℕ → Prop} {bw : Θ → ℕ} {q : ℕ → Tree → Prop}
    (hc : c.taken = false → coreProgram.Takes c.f c.args.length = true)
    (h : if c.taken then RelAtInWST S fs cert w rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ) bw (q b)
      else m = fs c.f) :
    ∃ k : Tree, Tree.KidsValidB S coreProgram rd σ [c] [k] ∧ k.BufsOk coreProgram ∧
      k.Placed coreProgram fs cert b ∧ k.total fs = m ∧ k.LoadsIn coreProgram fs cert Rk b ∧
      (c.taken = true → ∀ i, Dk i → k.Data coreProgram fs cert b i) ∧
      (∀ θ, k.weight (w θ) ≤ bw θ) ∧ (c.taken = true → q b k) := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at h
    obtain ⟨k, hq, hn, hv, hb, hp, htot, hl, hd, hw⟩ := h
    exact ⟨k, ⟨hn, by rw [ite_eq_left ht]; exact hv, trivial⟩, hb, hp, htot, hl, fun _ => hd, hw,
      fun _ => hq⟩
  · rw [ite_eq_right ht] at h
    obtain ⟨k, hkv, hkb, hkp, hkt, hkl, -⟩ := kidB_ofIn (P := coreProgram) (fs := fs) (cert := cert)
      (rd := rd) (σ := σ) (b := b) (m := m) (Rk := Rk) (Dk := Dk) hc
      (show (if c.taken then RelAtInB S coreProgram fs cert rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ)
        else m = fs c.f) by rw [ite_eq_right ht]; exact h)
    have hk := hkv.2.1
    rw [ite_eq_right ht] at hk
    obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
    exact ⟨_, hkv, hkb, hkp, hkt, hkl, fun h' => absurd h' ht, fun θ => by simp [Tree.weight],
      fun h' => absurd h' ht⟩

/-- **The callees of `KidsFromInWST`** (`kidsS_of_kidsFromInW`), their trees satisfying their
predicates at the positions they are placed (`KidsSat`). -/
theorem kidsST_of_kidsFromInWT (R : ℕ → Prop) : ∀ (cs : List Call) (bws : List (Θ → ℕ))
    (qs : List (ℕ → Tree → Prop)) (Dacc : ℕ → Prop) (b n : ℕ) (Dend : ℕ → Prop),
    (∀ c ∈ cs, c.taken = false → coreProgram.Takes c.f c.args.length = true) →
    KidsFromInWST S fs cert w rd σ R Dacc cs bws qs b n Dend →
    ∃ ks : List Tree, Tree.KidsValidB S coreProgram rd σ cs ks ∧ Tree.BufsOkKids coreProgram ks ∧
      Tree.PlacedKids coreProgram fs cert (bases b (ks.map (Tree.total fs))) ks ∧
      (ks.map (Tree.total fs)).sum = n ∧
      (∀ i, Dend i → Dacc i ∨ Tree.DataKids coreProgram fs cert (bases b (ks.map (Tree.total fs))) ks i) ∧
      (∀ Rp : ℕ → Prop, (∀ i, R i → Rp i) → (∀ i, Dacc i → Rp i) →
        (∀ i, Tree.DataKids coreProgram fs cert (bases b (ks.map (Tree.total fs))) ks i → Rp i) →
        Tree.LoadsInKids coreProgram fs cert Rp (bases b (ks.map (Tree.total fs))) ks) ∧
      (∀ θ, Tree.weightKids (w θ) ks ≤ (bws.map (· θ)).sum) ∧
      KidsSat cs qs (bases b (ks.map (Tree.total fs))) ks
  | [], _, _, Dacc, _, n, Dend, _, h => by
      rw [KidsFromInWST] at h
      refine ⟨[], by simp [Tree.KidsValidB], by rw [Tree.BufsOkKids]; trivial, placedKids_nil,
        by simp [h.1], fun i hi => Or.inl (h.2 i hi), fun _ _ _ _ => loadsInKids_nil,
        fun θ => by simp [Tree.weightKids], by simp [KidsSat]⟩
  | _ :: _, [], _, _, _, _, _, _, h => by rw [KidsFromInWST] at h; exact h.elim
  | _ :: _, _ :: _, [], _, _, _, _, _, h => by rw [KidsFromInWST] at h; exact h.elim
  | c :: cs, bw :: bws, q :: qs, Dacc, b, n, Dend, hw, h => by
      rw [KidsFromInWST] at h
      obtain ⟨m, n', Rk, Dk, rfl, hRk, hc, hcs⟩ := h
      obtain ⟨k, hkv, hkb, hkp, hkt, hkl, hkd, hkw, hkq⟩ := kidST_ofInW (hw c List.mem_cons_self) hc
      obtain ⟨ks, hv, hb, hp, hs, hd, hl, hws, hq⟩ := kidsST_of_kidsFromInWT R cs bws qs _ (b + m) n'
        Dend (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) hcs
      have hpos : bases b ((k :: ks).map (Tree.total fs)) = b :: bases (b + m) (ks.map (Tree.total fs)) := by
        rw [List.map_cons, bases, hkt]
      refine ⟨k :: ks, ⟨hkv.1, hkv.2.1, hv⟩, by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
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
      · intro θ
        have := hws θ
        have := hkw θ
        simp only [Tree.weightKids, List.map_cons, List.sum_cons]
        omega
      · rw [hpos]
        exact ⟨hkq, hq⟩

/-- **`relAtInWS_of_walk` with predicates**: the node of `f` at `σ`, its callees' trees satisfying
their predicates where they are placed, satisfies any predicate `Q` they give it. -/
theorem relAtInWST_of_walk {R D Dk : ℕ → Prop} {fp N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Memory.Ev} {vs : List V} {bws : List (Θ → ℕ)}
    {qs : List (ℕ → Tree → Prop)} {Q : Tree → Prop}
    (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false ∨ calls es = []) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.HoldsB S rd σ)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f) (allocs σ es)).map fun b => ofK (Parameters.gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (Parameters.gpow (fp + cert f q.2)))
    (hk : KidsFromInWST S fs cert w rd σ
      (fun i => R i ∨ ownData cert fp (fp + fs f) f (allocs σ es) es i)
      (fun _ => False) (calls es) bws qs (fp + fs f + (allocs σ es).sum) N Dk)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = Parameters.gpow i ∧
      (ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ R i ∨ Dk i))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ Dk i)
    (hQ : ∀ ks : List Tree, Tree.KidsValidB S coreProgram rd σ (calls es) ks →
      KidsSat (calls es) qs (bases (fp + fs f + (allocs σ es).sum) (ks.map (Tree.total fs))) ks →
      Q (Memory.Tree.node f σ (allocs σ es) ks)) :
    RelAtInWST S fs cert w rd R D fp (fs f + (allocs σ es).sum + N) f args rets
      (fun θ => w θ f + (bws.map (· θ)).sum) Q := by
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl, hkw, hkq⟩ :=
    kidsST_of_kidsFromInWT _ _ _ _ _ _ _ _
      (takes_of_calls coreProgram_wf (List.mem_of_find?_eq_some hf) hw) hk
  have hl' : coreProgram.loop f = false ∨ ks.map (Tree.total fs) = [] := by
    rcases hl with hl | hl
    · exact Or.inl hl
    · rw [hl] at hkv
      cases ks with
      | nil => exact Or.inr rfl
      | cons _ _ => exact hkv.elim
  obtain ⟨hbb, hkpos⟩ := kidPos_not_loop (P := coreProgram) (fs := fs) (fp := fp) (bufs := allocs σ es) hl'
  have hdata : ∀ i, (Memory.Tree.node f σ (allocs σ es) ks).Data coreProgram fs cert fp i ↔
      ownData cert fp (fp + fs f) f (allocs σ es) es i ∨
        Tree.DataKids coreProgram fs cert (bases (fp + fs f + (allocs σ es).sum) (ks.map (Tree.total fs))) ks i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos]
  refine ⟨Memory.Tree.node f σ (allocs σ es) ks, hQ ks hkv hkq, rfl,
    ⟨fn, hf, hp, es, vs, hw, hr, hes, hkv⟩, ?_, ?_, ?_, ?_, ?_,
    fun θ => by have := hkw θ; simp only [Tree.weight]; omega⟩
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

theorem kidsFromInWST_dend :
    ∀ (cs : List Call) (bws : List (Θ → ℕ)) (qs : List (ℕ → Tree → Prop)) (Dacc : ℕ → Prop)
      (b n : ℕ) {D D' : ℕ → Prop} {R : ℕ → Prop},
      (∀ i, D' i → D i) → KidsFromInWST S fs cert w rd σ R Dacc cs bws qs b n D →
      KidsFromInWST S fs cert w rd σ R Dacc cs bws qs b n D'
  | [], _, _, _, _, _, _, _, _, hD, ⟨hn, h⟩ => ⟨hn, fun i hi => h i (hD i hi)⟩
  | _ :: _, [], _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, h => h.elim
  | _ :: cs, _ :: bws, _ :: qs, _, _, _, _, _, _, hD, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
      ⟨m, n', Rk, Dk, hn, hR, hc, kidsFromInWST_dend cs bws qs _ _ _ hD hk⟩

/-- **`kidsFromInWS_append` with predicates.** -/
theorem kidsFromInWST_append {R : ℕ → Prop} :
    ∀ (cs1 cs2 : List Call) (bws1 bws2 : List (Θ → ℕ)) (qs1 qs2 : List (ℕ → Tree → Prop))
      (Dacc : ℕ → Prop) (b n1 n2 : ℕ) (D1 D : ℕ → Prop),
      bws1.length = cs1.length → qs1.length = cs1.length →
      KidsFromInWST S fs cert w rd σ R Dacc cs1 bws1 qs1 b n1 D1 →
      (∀ Dacc' : ℕ → Prop, (∀ i, D1 i → Dacc' i) →
        KidsFromInWST S fs cert w rd σ R Dacc' cs2 bws2 qs2 (b + n1) n2 D) →
      KidsFromInWST S fs cert w rd σ R Dacc (cs1 ++ cs2) (bws1 ++ bws2) (qs1 ++ qs2) b (n1 + n2) D
  | [], cs2, [], bws2, [], qs2, Dacc, b, n1, n2, D1, D, _, _, ⟨hn, hD⟩, h2 => by
    subst hn; simpa using h2 Dacc hD
  | [], _, _ :: _, _, _, _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | [], _, [], _, _ :: _, _, _, _, _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _ :: _, _, [], _, _, _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | _ :: _, _, _ :: _, _, [], _, _, _, _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _ :: cs1, cs2, _ :: bws1, bws2, _ :: qs1, qs2, Dacc, b, n1, n2, D1, D, hl, hl',
      ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩, h2 =>
    ⟨m, n' + n2, Rk, Dk, by omega, hR, hc,
      kidsFromInWST_append cs1 cs2 bws1 bws2 qs1 qs2 _ (b + m) n' n2 D1 D (by simpa using hl)
        (by simpa using hl') hk fun Dacc' h => by
          rw [show b + m + n' = b + n1 by omega]; exact h2 Dacc' h⟩

/-- **`kidsFromInWS_of_kidsW` with predicates.** -/
theorem kidsFromInWST_of_kidsW (κ : ℕ) : ∀ (ks : List Kid) (bs : List ℕ) (bws : List (Θ → ℕ))
    (Qs : List (ℕ → Reader → Tree → Prop)),
    KidsWST S fs cert w κ ks bs bws Qs → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      DisjL L ∧ N ≤ bs.sum ∧ OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInWST S fs cert w rd σ R Dacc cs bws (Qs.map fun Q b t => Q b rd t) b N
          (fun i => Dacc i ∨ outRegion ks outs i)
  | [], [], [], [], _, b => ⟨0, [], [], trivial, fun _ h => by simp at h, disj_nil, le_rfl, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | [], [], _ :: _, _, h, _ => h.elim
  | [], [], [], _ :: _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, _ :: _, [], h, _ => h.elim
  | k :: ks, B :: bs, Bw :: bws, Q :: Qs, ⟨hok, hnk, hks⟩, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hnb, hrel⟩ := hok ht b
      obtain ⟨N, L, outs, ho, hW, hD, hNb, hI, hK⟩ := kidsFromInWST_of_kidsW κ ks bs bws Qs hks (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, ⟨fun _ => hout, ho⟩, ?_,
        disj_append hd hD hw hW le_rfl, by simp only [List.sum_cons]; omega,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := memL_append.mp hL
          simp only [Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL k.Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [ht, ↓reduceIte]
            rw [hf, ha, hr]
            exact hrel rd hlow (memL_append.mpr ⟨hL1, hLk⟩)
          · refine kidsFromInWST_dend cs bws _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · have ht' : k.taken = false := by simpa using ht
      obtain ⟨N, L, outs, ho, hW, hD, hNb, hI, hK⟩ :=
        kidsFromInWST_of_kidsW κ ks bs bws Qs hks (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, by have := hnk ht'; simp only [List.sum_cons]; omega,
        ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · rw [hct, ht']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hf]
        · refine kidsFromInWST_dend cs bws _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL (memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

theorem kidsWST_of (κ : ℕ) (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) (qk : Kid → ℕ → Reader → Tree → Prop) :
    ∀ ks : List Kid,
    (∀ k ∈ ks, k.taken = true → CompleteAtWST S fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k) (qk k)) →
    KidsWST S fs cert w κ ks (ks.map fun k => if k.taken = true then bd k else fs k.f) (kidsWs bdw ks)
      (ks.map qk)
  | [], _ => trivial
  | k :: ks, h => by
      refine ⟨fun ht => ?_, fun ht => ?_, kidsWST_of κ bd bdw qk ks fun k' hk' => h k' (by simp [hk'])⟩
      · simp only [ht, ↓reduceIte]
        exact (h k (by simp) ht).wmono fun θ => by simp
      · simp [ht]

/-- **`kidsFromInWS_of_kidsBW` with predicates**: callees complete with predicates `qk` give
`KidsFromInWST` at `ks.map qk`. -/
theorem kidsFromInWST_of_kidsBW (κ : ℕ) (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ)
    (qk : Kid → ℕ → Reader → Tree → Prop) (ks : List Kid)
    (hok : ∀ k ∈ ks, k.taken = true →
      CompleteAtWST S fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k) (qk k))
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      DisjL L ∧ N ≤ kidsBound fs bd ks ∧ OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInWST S fs cert w rd σ R Dacc cs (kidsWs bdw ks)
          (ks.map fun k b t => qk k b rd t) b N (fun i => Dacc i ∨ outRegion ks outs i) := by
  obtain ⟨N, L, outs, ho, hW, hD, hN, hI, hK⟩ :=
    kidsFromInWST_of_kidsW κ ks _ _ _ (kidsWST_of κ bd bdw qk ks hok) b
  refine ⟨N, L, outs, ho, hW, hD, ?_, hI, fun rd σ cs R Dacc hc hl hL hLin hR => ?_⟩
  · simpa [kidsBound] using hN
  · have := hK rd σ cs R Dacc hc hl hL hLin hR
    simpa [List.map_map, Function.comp_def] using this

end Compose

end
end LeanVM.Guest.B1
