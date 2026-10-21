/-
  LeanVM.Guest.B1.Main.TreeLoopT

  Loops in the uniform placed form within weights under any semantics, their trees satisfying a
  predicate: `WeightAtS.lean`'s and `WeightLoopS.lean`'s loop lemmas with `Comp/TreeRoot.lean`'s
  tree predicates.
-/

module

public import LeanVM.Guest.B1.Comp.TreeRoot
public import LeanVM.Guest.B1.Main.WeightLoopS

/-!
# Loops with tree predicates

`relAtInWS_of_walk_loop`, `loopStepS_bufsW` and `completeAtS_loopW` keep only that some tree
exists. Here their trees satisfy predicates:

* `relAtInWST_of_walk_loop`: a loop's node, its front callees' trees satisfying `KidsSat` and its
  tail's tree satisfying `qt`, satisfies any predicate `Q` they give it;
* `loopStepS_bufsWT`: one iteration with `HeapBuf`s, its callees `KidsWST`, the iteration's node
  satisfying `Q rd` from its valuation, its callees' and its tail's trees;
* `completeAtS_loopWT`: the iterations `j < m` chained, iteration `j`'s tree at `fp` satisfying
  `LQ j fp rd`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB Returns Kid CallsMatch
  OutsOk OutsIn RegionsOk outRegion kidsBound within_append kidsFromIn_dend bufL RelAtInWST
  CompleteAtWST KidsFromInWST KidsWST KidsSat kidsST_of_kidsFromInWT kidST_ofInW kidsFromInWST_of_kidsW
  kidsFromInWST_dend)

@[expose] public section

variable {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ}

/-- `RelAtInWS.dmono` with a predicate. -/
theorem RelAtInWST.dmono {rd : Reader} {R D D' : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Bw : Θ → ℕ} {Q : Tree → Prop} (h : RelAtInWST S fs cert w rd R D fp n f args rets Bw Q)
    (hD : ∀ i, D' i → D i) : RelAtInWST S fs cert w rd R D' fp n f args rets Bw Q :=
  let ⟨t, hq, hn, hv, hb, hp, ht, hl, hd, hw⟩ := h
  ⟨t, hq, hn, hv, hb, hp, ht, hl, fun i hi => hd i (hD i hi), hw⟩

/-- `RelAtInWS.wmono` with a predicate. -/
theorem RelAtInWST.wmono {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Bw Bw' : Θ → ℕ} {Q : Tree → Prop} (h : RelAtInWST S fs cert w rd R D fp n f args rets Bw Q)
    (hB : ∀ θ, Bw θ ≤ Bw' θ) : RelAtInWST S fs cert w rd R D fp n f args rets Bw' Q :=
  let ⟨t, hq, hn, hv, hb, hp, ht, hl, hd, hw⟩ := h
  ⟨t, hq, hn, hv, hb, hp, ht, hl, hd, fun θ => (hw θ).trans (hB θ)⟩

/-- A tree predicate weakened. -/
theorem RelAtInWST.qmono {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Bw : Θ → ℕ} {Q Q' : Tree → Prop} (h : RelAtInWST S fs cert w rd R D fp n f args rets Bw Q)
    (hQ : ∀ t, Q t → Q' t) : RelAtInWST S fs cert w rd R D fp n f args rets Bw Q' :=
  let ⟨t, hq, hn, hv, hb, hp, ht, hl, hd, hw⟩ := h
  ⟨t, hQ t hq, hn, hv, hb, hp, ht, hl, hd, hw⟩

/-- **The callee at call `i`**: on callees valid at the calls and as many positions, an entered
call's tree and position satisfy its predicate. -/
theorem kidsSat_get {S : BlakeSem} {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Call} {qs : List (ℕ → Tree → Prop)} {bs : List ℕ} {ks : List Tree},
      Tree.KidsValidB S P rd σ cs ks → qs.length = cs.length → bs.length = ks.length →
      KidsSat cs qs bs ks → ∀ i (hi : i < cs.length), cs[i].taken = true →
        ∃ (k : Tree) (b : ℕ) (q : ℕ → Tree → Prop), ks[i]? = some k ∧ bs[i]? = some b ∧
          qs[i]? = some q ∧ q b k
  | [], _, _, _, _, _, _, _, i, hi, _ => absurd hi (by simp)
  | _ :: _, [], _, _, _, hq, _, _, _, _, _ => absurd hq (by simp)
  | _ :: _, _ :: _, _, [], hv, _, _, _, _, _, _ => by simp [Tree.KidsValidB] at hv
  | _ :: _, _ :: _, [], _ :: _, _, _, hb, _, _, _, _ => absurd hb (by simp)
  | c :: cs, q :: qs, b :: bs, k :: ks, hv, hq, hb, hs, i, hi, ht => by
      simp only [Tree.KidsValidB, KidsSat] at hv hs
      cases i with
      | zero => exact ⟨k, b, q, rfl, rfl, rfl, hs.1 ht⟩
      | succ i =>
          obtain ⟨k', b', q', h1, h2, h3, h4⟩ := kidsSat_get hv.2.2 (by simpa using hq) (by simpa using hb)
            hs.2 i (by simpa using hi) ht
          exact ⟨k', b', q', by simpa using h1, by simpa using h2, by simpa using h3, h4⟩

section Compose

variable {rd : Reader} {σ : Val}

/-- **`relAtInWS_of_walk_loop` with predicates**: the node of a loop at `σ`, its front callees'
trees satisfying their predicates where they are placed and its tail's `qt`, satisfies any
predicate `Q` they give it. -/
theorem relAtInWST_of_walk_loop {R D Dk Rt Dt : ℕ → Prop} {fp m N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {cs : List Call} {c : Call}
    {bws : List (Θ → ℕ)} {bt : Θ → ℕ} {qs : List (ℕ → Tree → Prop)} {qt : Tree → Prop}
    {Q : Tree → Prop}
    (hf : coreProgram.find? f = some fn) (hl : coreProgram.loop f = true) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.HoldsB S rd σ)
    (hc : calls es = cs ++ [c])
    (htail : if c.taken then RelAtInWST S fs cert w rd Rt Dt (fp + fs f) m c.f (c.args.map σ)
      (c.rets.map σ) bt qt else m = fs c.f)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f + m) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromInWST S fs cert w rd σ
      (fun i => R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i)
      (fun _ => False) cs bws qs (fp + fs f + m + (allocs σ es).sum) N Dk)
    (hRt : ∀ i, Rt i → R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ R i ∨ Dk i ∨ (c.taken = true ∧ Dt i)))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i ∨
      (c.taken = true ∧ Dt i))
    (hQ : ∀ (ks : List Tree) (k : Tree), Tree.KidsValidB S coreProgram rd σ cs ks →
      KidsSat cs qs (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))) ks →
      (c.taken = true → qt k) → k.total fs = m → Q (Memory.Tree.node f σ (allocs σ es) (ks ++ [k]))) :
    RelAtInWST S fs cert w rd R D fp (fs f + m + (allocs σ es).sum + N) f args rets
      (fun θ => w θ f + (bws.map (· θ)).sum + bt θ) Q := by
  have htk := takes_of_calls coreProgram_wf (List.mem_of_find?_eq_some hf) hw
  rw [hc] at htk
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl, hkw, hkq⟩ := kidsST_of_kidsFromInWT _ _ _ _ _ _ _ _
    (fun c' hc' => htk c' (List.mem_append_left _ hc')) hk
  obtain ⟨k, hkv', hkb', hkp', hkt, hkl', hkd', hkw', hkq'⟩ :=
    kidST_ofInW (q := fun _ => qt) (htk c (List.mem_append_right _ List.mem_cons_self)) htail
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
        Tree.DataKids coreProgram fs cert (bases (fp + fs f + m + (allocs σ es).sum)
          (ks.map (Tree.total fs))) ks i ∨
        k.Data coreProgram fs cert (fp + fs f) i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos, dataKids_append hlen, dataKids_cons]
    simp only [not_dataKids_nil, or_false]
  refine ⟨Memory.Tree.node f σ (allocs σ es) (ks ++ [k]), hQ ks k hkv hkq hkq' hkt, rfl,
    ⟨fn, hf, hp, es, vs, hw, hr, hes, by rw [hc]; exact kidsValidB_append hkv hkv'⟩, ?_, ?_, ?_, ?_, ?_,
    fun θ => ?_⟩
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
    have hDt : ∀ i, c.taken = true ∧ Dt i →
        (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i :=
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
  · have h1 := hkw θ
    have h2 := hkw' θ
    simp only [Tree.weight, weightKids_append, Tree.weightKids]
    omega

end Compose

/-- **`loopStepS_bufsW` with predicates**: one iteration with `HeapBuf`s, its callees `KidsWST`
with predicates `Qs`, its tail's tree satisfying `qt rd`: the iteration's node satisfies `Q rd`
when the valuation `hσ` chooses gives it from its callees' and its tail's trees. -/
theorem loopStepS_bufsWT {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) {pre : List Stmt} (hb : fn.body = pre ++ [.ret []])
    (hs : pre.all Stmt.straight = true) (AL : List (V × (ℕ ⊕ V))) (hal : pre.filterMap Stmt.allocSz = AL)
    (had : pre.filterMap Stmt.addrS = []) (κ : ℕ) (Lin : Layout) (args : List E)
    (fronts : List (Option V × String × List V × List V)) (tc : V) (targs : List V)
    (hcs : pre.filterMap Stmt.callS = fronts ++ [(some tc, f, targs, [])])
    (sizes : List ℕ) (bufs : List (List E)) (hbl : List.Forall₂ (fun c s => c.length ≤ s) bufs sizes)
    (fp mt : ℕ) (ks : List Kid) (bs : List ℕ) (bws : List (Θ → ℕ))
    (Qs : List (ℕ → Reader → Tree → Prop)) (hks : KidsWST S fs cert w κ ks bs bws Qs)
    (hsub : ∀ k ∈ ks, SubL k.Lin (bufL (fp + fs f + mt) sizes bufs ++ Lin))
    (targs' : List E) (more : Bool) (qt Q : Reader → Tree → Prop)
    (hσ : ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f + mt) sizes bufs ++ Lin) → ∀ outs, OutsOk ks outs →
      ∃ σ : Val, fn.params.map σ = args ∧
      Stmt.HoldsListB S (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = []) ∧
      AL.map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
      (AL.map Prod.fst).map σ = (bases (fp + fs f + mt) sizes).map (fun b => ofK (gpow b)) ∧
      CallsMatch σ (fronts.map (mkCall σ)) ks outs ∧ decide (σ tc ≠ 0) = more ∧
      targs.map σ = targs' ∧
      (∀ q ∈ pre.filterMap LeanVM.Guest.B1.Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
        (RegionL Lin i ∨ RegionL (bufL (fp + fs f + mt) sizes bufs) i)) ∧
      ∀ (kts : List Tree) (k : Tree),
        Tree.KidsValidB S coreProgram rd σ (fronts.map (mkCall σ)) kts →
        KidsSat (fronts.map (mkCall σ)) (Qs.map fun Q b t => Q b rd t)
          (bases (fp + fs f + mt + sizes.sum) (kts.map (Tree.total fs))) kts →
        (more = true → qt rd k) → k.total fs = mt → Q rd (Memory.Tree.node f σ sizes (kts ++ [k]))) :
    ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧ n ≤ sizes.sum + bs.sum ∧
      ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) → ∀ bt : Θ → ℕ,
        (more = true → RelAtInWST S fs cert w rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          targs' [] bt (qt rd)) →
        (more = false → mt = fs f) →
        RelAtInWST S fs cert w rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f args []
          (fun θ => w θ f + (bws.map (· θ)).sum + bt θ) (Q rd) := by
  set Lb := bufL (fp + fs f + mt) sizes bufs with hLb
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInWST_of_kidsW κ ks bs bws Qs hks
    (fp + fs f + mt + sizes.sum)
  refine ⟨sizes.sum + N, Lb ++ L, ?_,
    disj_append (bufL_disj _ _ _ hbl) hD (LeanVM.Guest.B1.bufL_within _ _ _ hbl) hW le_rfl,
    by omega, fun rd hlow hL bt htail hnot => ?_⟩
  · rw [within_append]
    exact ⟨(LeanVM.Guest.B1.bufL_within _ _ _ hbl).mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
  rw [List.append_assoc] at hL
  obtain ⟨hLb, hL'⟩ := memL_append.mp hL
  obtain ⟨hL1, hL2⟩ := memL_append.mp hL'
  obtain ⟨σ, hp, hH, hsz, hdst, hcm, htk, hta, hld, hQ⟩ :=
    hσ rd hlow (memL_append.mpr ⟨hLb, hL2⟩) outs ho
  have hwf : Stmt.wfList coreProgram fn.body = true :=
    coreProgram_wf fn (List.mem_of_find?_eq_some hf)
  have hw := walk_straight σ [] pre hs
  rw [← hb] at hw
  have hsat := walkB_sat fn.body hwf hH
  rw [hw] at hsat
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ pre hs
  rw [hal] at e1 e2
  have hsz' := e2.trans hsz
  rw [had] at e3
  rw [hcs, List.map_append] at e4
  have hld' := LeanVM.Guest.B1.loadAddrs_straight σ pre hs
  have hc : (mkCall σ (some tc, f, targs, [])).taken = more := htk
  have hown : ∀ i, RegionL Lb i → ownData cert fp (fp + fs f + mt) f (allocs σ (pre.flatMap (slEvs σ)))
      (pre.flatMap (slEvs σ)) i := fun i hi => by
    rw [hsz']
    exact Or.inl (LeanVM.Guest.B1.bufL_region _ _ _ hbl i hi)
  have := relAtInWST_of_walk_loop (fs := fs) (cert := cert) (w := w) (R := RegionL Lin)
    (D := fun _ => False) (Dk := fun i => False ∨ outRegion ks outs i) (Rt := RegionL Lin)
    (Dt := fun _ => False) (fp := fp) (m := mt) (N := N) (σ := σ) (rd := rd) (bws := bws) (bt := bt)
    (qs := Qs.map fun Q b t => Q b rd t) (qt := qt rd) (Q := Q rd)
    hf hl hp hw rfl
    (fun e he => (hsat.1 e he).1) e4 ?_ (by rw [e1, hsz']; exact hdst) (by rw [e3]; simp) ?_
    (fun i hi => Or.inl hi) ?_ (fun i hi => hi.elim) ?_
  · rwa [hsz', Nat.add_assoc] at this
  · cases more with
    | true =>
      simp only [hc, ↓reduceIte]
      simp only [mkCall, List.map_nil]
      rw [hta]
      exact htail rfl
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact hnot rfl
  · have hsum : (allocs σ (pre.flatMap (slEvs σ))).sum = sizes.sum := by rw [hsz']
    rw [hsum]
    exact hK rd σ _ _ (fun _ => False) hcm hlow hL1
      (LeanVM.Guest.B1.memL_lins fun k hk => (hsub k hk).1 rd (memL_append.mpr ⟨hLb, hL2⟩))
      (regionsOk_of_sub _ _ _ fun k hk i hi =>
        (regionL_append_or ((hsub k hk).2 i hi)).elim (fun h => Or.inr (hown i h)) Or.inl)
  · intro A hA
    rw [hld', List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    obtain ⟨i, hi, hr⟩ := hld q hq
    exact ⟨i, hi, hr.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inl (hown i h)⟩
  · intro kts k hkv hsat' ht hkt
    have hsum : (allocs σ (pre.flatMap (slEvs σ))).sum = sizes.sum := by rw [hsz']
    rw [hsum] at hsat'
    rw [hsz']
    exact hQ kts k hkv hsat' (fun h => ht (by rw [hc]; exact h)) hkt

/-- **`completeAtS_loopW` with predicates**: iteration `j`'s tree at `fp` satisfies `LQ j fp rd`,
each step giving it from its tail's. -/
theorem completeAtS_loopWT {f : String} (κ : ℕ) (Lin : Layout) (A : ℕ → List E) (m : ℕ)
    (bs : ℕ → ℕ) (bws : ℕ → Θ → ℕ) (LQ : ℕ → ℕ → Reader → Tree → Prop)
    (step : ∀ j < m, ∀ fp mt : ℕ, ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧
      n ≤ bs j ∧ ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) → ∀ bt : Θ → ℕ,
        (j + 1 < m → RelAtInWST S fs cert w rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          (A (j + 1)) [] bt (LQ (j + 1) (fp + fs f) rd)) →
        (j + 1 = m → mt = fs f) →
        RelAtInWST S fs cert w rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f (A j) []
          (fun θ => w θ f + bws j θ + bt θ) (LQ j fp rd)) :
    ∀ j < m, CompleteAtWST S fs cert w κ f Lin (A j) (Returns []) (loopSum (fs f) bs j (m - j))
      (fun θ => loopSum (w θ f) (fun i => bws i θ) j (m - j)) (LQ j) := by
  have key : ∀ t j, j + t + 1 = m →
      CompleteAtWST S fs cert w κ f Lin (A j) (Returns []) (loopSum (fs f) bs j (t + 1))
        (fun θ => loopSum (w θ f) (fun i => bws i θ) j (t + 1)) (LQ j) := by
    intro t
    induction t with
    | zero =>
      intro j hj fp
      obtain ⟨n, L, hW, hD, hn, hS⟩ := step j (by omega) fp (fs f)
      refine ⟨fs f + fs f + n, L, [], [], ⟨rfl, rfl⟩, ?_, by simpa using hD,
        by simp only [loopSum]; omega, fun rd hl hL => ?_⟩
      · simpa using hW.mono (by omega) (by omega)
      · refine RelAtInWST.wmono (RelAtInWST.dmono (hS rd hl (by simpa using hL) (fun θ => w θ f)
          (fun h => by omega) (fun _ => rfl)) fun i hi => ?_) fun θ => ?_
        · obtain ⟨q, hq, _⟩ := hi; simp at hq
        · simp only [loopSum]; omega
    | succ t ih =>
      intro j hj fp
      obtain ⟨nt, Lt, rt, Lo, ⟨rfl, rfl⟩, hWt, hDt, hnt, hSt⟩ := ih (j + 1) (by omega) (fp + fs f)
      obtain ⟨n, L, hW, hD, hn, hS⟩ := step j (by omega) fp nt
      simp only [List.nil_append] at hWt hDt
      refine ⟨fs f + nt + n, Lt ++ L, [], [], ⟨rfl, rfl⟩, ?_,
        by simpa using disj_append hDt hD hWt hW le_rfl,
        by rw [loopSum]; omega, fun rd hl hL => ?_⟩
      · simp only [List.nil_append]
        rw [within_append]
        exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
      · simp only [List.nil_append, List.append_assoc] at hL
        obtain ⟨hL1, hL2⟩ := memL_append.mp hL
        refine RelAtInWST.wmono (RelAtInWST.dmono (hS rd hl hL2
          (fun θ => loopSum (w θ f) (fun i => bws i θ) (j + 1) (t + 1))
          (fun _ => ?_) (fun h => by omega)) fun i hi => ?_) fun θ => ?_
        · refine RelAtInWST.dmono (hSt rd hl (by simpa using memL_append.mpr ⟨hL1, (memL_append.mp hL2).2⟩))
            fun i hi => ?_
          exact hi.elim
        · obtain ⟨q, hq, _⟩ := hi; simp at hq
        · conv_rhs => rw [loopSum]
  intro j hj
  have := key (m - 1 - j) j (by omega)
  rwa [show m - 1 - j + 1 = m - j by omega] at this

end
end LeanVM.Guest.B1.Main
