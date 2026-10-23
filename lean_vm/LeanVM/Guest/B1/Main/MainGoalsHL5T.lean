/-
  LeanVM.Guest.B1.Main.MainGoalsHL5T

  `main`'s honest children loop, its trees exposed: each iteration's node and its hinted counts
  (`MainGoalL5T … (L5Hinted w)`).
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5
public import LeanVM.Guest.B1.Main.MainHonestT

/-!
# The children loop's trees

`relAtInWT_of_walk_loop`: `relAtIn_of_walk_loop` (`Memory/Regions.lean`, same proof) by the node at
the walk's valuation, its tail call's tree satisfying a predicate. `L5Node k b Tt`: a `__loop5`
node whose valuation holds child `k`'s hinted counts (`child_meta` at `v20`, `v21`;
`child_da_count` at `v63`), its last child (the tail call's tree) satisfying `Tt` when `b`.
`L5From ex es ed m c`: the `m` iterations from child `c`, each `L5Node`. `l5_stepAtT`,
`l5_completeAtT`: `l5_stepAt`, `l5_completeAt` (same proofs) with those trees. `L5Hinted w`: the
honest run's, child `c`'s counts its statement's lists' lengths. `mainGoalL5T`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader} {σ : Val}

/-- **Composition with regions, a loop helper, its tail's tree exposed**: `relAtIn_of_walk_loop`
by the node at the walk's valuation, its last child the tail call's tree, satisfying `Tt` when the
call is taken. -/
theorem relAtInWT_of_walk_loop (hP : P.Wf) {R D Dk Rt Dt : ℕ → Prop} {fp m N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {cs : List Call} {c : Call} {Tt : Tree → Prop}
    (hf : P.find? f = some fn) (hl : P.loop f = true) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hc : calls es = cs ++ [c])
    (htail : if c.taken then RelAtInT P fs cert rd Rt Dt (fp + fs f) m c.f (c.args.map σ) (c.rets.map σ) Tt
      else m = fs c.f)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f + m) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromIn P fs cert rd σ (fun i => R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i)
      (fun _ => False) cs (fp + fs f + m + (allocs σ es).sum) N Dk)
    (hRt : ∀ i, Rt i → R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ R i ∨ Dk i ∨ (c.taken = true ∧ Dt i)))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i ∨
      (c.taken = true ∧ Dt i)) :
    RelAtInT P fs cert rd R D fp (fs f + m + (allocs σ es).sum + N) f args rets
      (fun t => ∃ ks k, t = .node f σ (allocs σ es) (ks ++ [k]) ∧ (c.taken = true → Tt k)) := by
  have htk := takes_of_calls hP (List.mem_of_find?_eq_some hf) hw
  rw [hc] at htk
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl⟩ := kids_of_kidsFromIn _ _ _ _ _ _
    (fun c' hc' => htk c' (List.mem_append_left _ hc')) hk
  obtain ⟨k, hkv', hkb', hkp', hkt, hkl', hkd', hkT⟩ :=
    kid_ofInT (htk c (List.mem_append_right _ List.mem_cons_self)) htail
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
  refine ⟨.node f σ (allocs σ es) (ks ++ [k]), ⟨rfl,
    ⟨fn, hf, hp, es, vs, hw, hr, hes, by rw [hc]; exact kidsValid_append hkv hkv'⟩, ?_, ?_, ?_, ?_, ?_⟩,
    ks, k, rfl, hkT⟩
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

end
end LeanVM.Guest.Memory

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest (Limits)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds regionL_of_mem limb0_gen_pow_mul exists_of_length_succ
  fn_name_of_find)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT Returns Kid OutsOk CallsMatch RegionsOk outRegion
  DisjL Within disj_append disj_nil kidsFromIn_of_kidsD regionsOk_of within_append bufL bufL_within
  bufL_disj bufL_region LowDef)

@[expose] public section

/-- **A `__loop5` node holding child `k`'s hinted counts**: `child_meta`'s `g^ex`, `g^es` at `v20`,
`v21`, `child_da_count`'s `g^ed` at `v63`; its last child (the tail call's tree) satisfies `Tt`
when `b`. -/
def L5Node (k : KidH) (b : Prop) (Tt : Tree → Prop) (t : Tree) : Prop :=
  ∃ σ bufs ks k', t = .node "__loop5" σ bufs (ks ++ [k']) ∧ σ (.n 20) = gen ^ k.ex ∧
    σ (.n 21) = gen ^ k.es ∧ σ (.n 63) = gen ^ k.ed ∧ (b → Tt k')

/-- **The `m` iterations from child `c`**, each a `__loop5` node holding its child's hinted counts
(`ex c`, `es c`, `ed c`), the next iteration its last child. -/
def L5From (ex es ed : ℕ → ℕ) : ℕ → ℕ → Tree → Prop
  | 0, _, _ => True
  | m + 1, c, t => ∃ σ bufs ks k, t = .node "__loop5" σ bufs (ks ++ [k]) ∧ σ (.n 20) = gen ^ ex c ∧
      σ (.n 21) = gen ^ es c ∧ σ (.n 63) = gen ^ ed c ∧ (m ≠ 0 → L5From ex es ed m (c + 1) k)

/-- **The honest children loop's trees**: iteration `c < nc` is a `__loop5` node whose hinted
counts are child `c`'s statement's lists' lengths, in the exponent (`g^|xmss|`, `g^|sphincs|`,
`g^|da|`), the next iteration its last child. -/
def L5Hinted (w : NodeWitness) : Tree → Prop :=
  L5From (hEx w) (hEs w) (hEd w) w.children.length 0

theorem completeAtDT_mono {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Lin : Layout} {args : List E} {Out : List E → Layout → Prop} {T T' : Tree → Prop}
    (h : CompleteAtDT fs cert κ f Lin args Out T) (hT : ∀ t, T t → T' t) :
    CompleteAtDT fs cert κ f Lin args Out T' := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hTt⟩ := hr rd hl hm
    ⟨t, ht, hT t hTt⟩⟩

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **One child of `__loop5`, placed, its tree exposed**: `l5_stepAt` (same proof), by the node
at the block's valuation, its hinted counts `k`'s, its tail call's tree satisfying `Tt`. -/
theorem l5_stepAtT {Lin : Layout} {W Pi Cr R C n nk c : ℕ}
    {lxt cover lxs lst lss s0 s1 glp gsq cfresh : E} {k : KidH} {Tt : Tree → Prop}
    (hn : n ≤ 2 ^ 16) (hnk : nk < 2 ^ 34) (hc : c + 1 ≤ nk) (hs01 : AllCanonical [s0, s1])
    (hk : KidOkC fs cert Lin W Pi Cr R C n lxt cover lxs lst lss s0 s1 glp gsq cfresh c k)
    (htail : c + 1 < nk → CompleteAtDT fs cert 16 "__loop5" Lin
      [gen ^ (c + 1), gen ^ nk, gen ^ W, lxt, cover, lxs, lst, lss, gen ^ Cr, gen ^ R, gen ^ C,
        gen ^ n, s0, s1, gen ^ Pi, glp, gsq, cfresh] (Returns []) Tt) :
    CompleteAtDT fs cert 16 "__loop5" Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, lss, gen ^ Cr, gen ^ R, gen ^ C,
        gen ^ n, s0, s1, gen ^ Pi, glp, gsq, cfresh] (Returns []) (L5Node k (c + 1 < nk) Tt) := by
  intro fp
  -- the rest of the loop
  obtain ⟨nt, Lt, hWt, hDt, hRt⟩ : ∃ nt Lt, Within Lt (fp + fs "__loop5") nt ∧ DisjL Lt ∧
      ∀ rd, LowDef 16 rd → MemL rd (Lt ++ Lin) →
        if decide (c + 1 ≠ nk) = true then
          RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL []) (fp + fs "__loop5") nt "__loop5"
            [gen ^ (c + 1), gen ^ nk, gen ^ W, lxt, cover, lxs, lst, lss, gen ^ Cr, gen ^ R, gen ^ C,
              gen ^ n, s0, s1, gen ^ Pi, glp, gsq, cfresh] [] Tt
        else nt = fs "__loop5" := by
    by_cases hlast : c + 1 = nk
    · exact ⟨fs "__loop5", [], fun q hq => by simp at hq, List.Pairwise.nil, fun _ _ _ => by
        simp [hlast]⟩
    · obtain ⟨nt, Lt, rt, Lot, ⟨rfl, rfl⟩, hW, hD, hR⟩ := htail (by omega) (fp + fs "__loop5")
      refine ⟨nt, Lt, by simpa using hW, by simpa using hD, fun rd hl hm => ?_⟩
      simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte]
      exact hR rd hl (by simpa using hm)
  -- the child's buffers
  set P1 := fp + fs "__loop5" + nt with hP1
  have hcdal := length_cdaW hk.root_len
  set Own : Layout := bufL P1 [2, 4 * k.ed] [[k.sp.1, k.sp.2], k.cdaW] with hOwn
  have hfit : List.Forall₂ (fun c s => c.length ≤ s) [[k.sp.1, k.sp.2], k.cdaW] [2, 4 * k.ed] := by
    simp [hcdal]
  have hOwn_eq : Own = [(P1, [k.sp.1, k.sp.2]), (P1 + 2, k.cdaW)] := rfl
  have hWo : Within Own P1 [2, 4 * k.ed].sum := bufL_within _ _ _ hfit
  -- the callees
  have hed34 : k.ed < 2 ^ 34 := by have := hk.ed_le; omega
  let ks : List Kid :=
    [⟨"child_claim_list_digest", true, [lxt, cover, k.base, 1, lxs, gen ^ k.ex], Lin,
        Returns [k.cx.1, k.cx.2]⟩,
      ⟨"child_claim_list_digest", true, [lst, cover, k.base * gen ^ k.ex, lxs, lss, gen ^ k.es], Lin,
        Returns [k.cs.1, k.cs.2]⟩,
      ⟨"__loop28", decide (k.ed ≠ 0), [1, gen ^ k.ed, gen ^ (P1 + 2), gen ^ R, gen ^ C, gen ^ n,
        k.base, gen ^ k.ex * gen ^ k.es], Lin ++ Own, Returns []⟩,
      ⟨"da_list_digest", true, [gen ^ (P1 + 2), gen ^ k.ed], Own, Returns [k.dl.1, k.dl.2]⟩,
      ⟨"statement_digest", true, [s0, s1, gen ^ P1, k.dl.1, k.dl.2, gen ^ Cr * gen ^ (24 * c)],
        Lin ++ Own, Returns [(k.pi s0 s1).1, (k.pi s0 s1).2]⟩,
      ⟨"verify_sub", true, [(k.pi s0 s1).1, (k.pi s0 s1).2, s0, s1, glp, gsq,
        cfresh * gen ^ (24 * c)], Lin, Returns []⟩]
  have mSp : (P1, [k.sp.1, k.sp.2]) ∈ Own := List.mem_cons_self
  have mCda : (P1 + 2, k.cdaW) ∈ Own := List.mem_cons_of_mem _ List.mem_cons_self
  have hcda : ∀ rd, MemL rd Own → ReadsAt rd (gen ^ (P1 + 2)) k.cdaW := fun rd hm => by
    rw [gen_pow_eq_ofK]; exact hm (P1 + 2, k.cdaW) mCda
  have hspm : ∀ rd, MemL rd Own → ReadsAt rd (gen ^ P1) [k.sp.1, k.sp.2] := fun rd hm => by
    rw [gen_pow_eq_ofK]; exact hm (P1, [k.sp.1, k.sp.2]) mSp
  have hok : ∀ kd ∈ ks, kd.taken = true → CompleteAtD fs cert 16 kd.f kd.Lin kd.args kd.Out := by
    intro kd hkd ht
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hkd
    rcases hkd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hk.hX
    · exact hk.hS
    · simp only [decide_eq_true_eq] at ht
      have := l28_completeAt fs cert (A := P1 + 2) (R := R) (C := C) (n := n) (ed := k.ed)
        (base := k.base) (nsub := gen ^ k.ex * gen ^ k.es) (Lin := Lin ++ Own) (slot := k.slot)
        (r := k.root) hn hed34 (fun d _ => hk.root_len d) hk.slot_lt
        (fun rd hm d hd => by
          obtain ⟨h1, h2⟩ := Main.memL_append.mp hm
          obtain ⟨-, -, -, -, -, hroots⟩ := hk.mem rd h1
          refine ⟨(hroots d hd).1, (hroots d hd).2, ?_⟩
          have := Main.readsAt_flatMap_of (List.range k.ed) (fun a _ => hk.root_len a) (hcda rd h2) d
            (by simpa using hd)
          simp only [List.getElem_range] at this
          rwa [← pow_add] at this)
        (fun d hd => by
          obtain ⟨-, -, -, -, hr⟩ := hk.reg
          refine ⟨regionL_append_left (hr d hd).1, fun i hi => regionL_append_left ((hr d hd).2 i hi),
            fun i hi => regionL_append_right ?_⟩
          have := regionL_of_mem (L := Own) (b := P1 + 2) (xs := k.cdaW) mCda
            (k := 4 * d + i) (by rw [hcdal]; omega)
          rwa [Nat.add_assoc]) 0 (by omega)
      rwa [pow_zero] at this
    · exact daList_completeAt fs cert fun rd hm =>
        ⟨k.ed, hk.ed_le, rfl, k.cdaW, hcdal, hcda rd hm, hk.cda_can, rfl⟩
    · refine statement_completeAt fs cert fun rd hm => ?_
      obtain ⟨h1, h2⟩ := Main.memL_append.mp hm
      obtain ⟨-, -, -, -, hdef, -⟩ := hk.mem rd h1
      have hs := hspm rd h2
      refine ⟨k.sp.1, k.sp.2, k.defer, hs 0 (by simp), hs 1 (by simp), hk.defer_len,
        by rw [← pow_add]; exact hdef, ?_, rfl⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hs01 _ (by simp)
      · exact hs01 _ (by simp)
      · exact (digestScalars_canonical _).1
      · exact (digestScalars_canonical _).2
      · exact (digestScalars_canonical _).1
      · exact (digestScalars_canonical _).2
    · exact hk.hV
  obtain ⟨Nk, Lk, outs, hoo, hW, hD, -, hKids⟩ :=
    kidsFromIn_of_kidsD (fs := fs) (cert := cert) 16 ks hok (P1 + [2, 4 * k.ed].sum)
  have hl0 : outs.length = 6 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
  obtain ⟨o4, t4, rfl, hl4⟩ := exists_of_length_succ hl3
  obtain ⟨o5, t5, rfl, hl5⟩ := exists_of_length_succ hl4
  obtain ⟨o6, t6, rfl, hl6⟩ := exists_of_length_succ hl5
  obtain rfl := List.eq_nil_of_length_eq_zero hl6
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hoo
  -- the layout
  have hWto : Within (Lt ++ Own) (fp + fs "__loop5") (nt + [2, 4 * k.ed].sum) := by
    rw [within_append]
    exact ⟨hWt.mono le_rfl (by omega), hWo.mono (by omega) (by omega)⟩
  refine ⟨fs "__loop5" + nt + [2, 4 * k.ed].sum + Nk, Lt ++ Own ++ Lk, [], [], ⟨rfl, rfl⟩, ?_,
    by rw [List.nil_append]; exact disj_append (disj_append hDt (bufL_disj _ _ _ hfit : DisjL Own)
      hWt hWo le_rfl) hD hWto hW (by omega), fun rd hlow hm => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hWto.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin⟩ := Main.memL_append.mp hm
  obtain ⟨hm2, hLk⟩ := Main.memL_append.mp hm1
  obtain ⟨hmt, hmo⟩ := Main.memL_append.mp hm2
  have ht := hRt rd hlow (Main.memL_append.mpr ⟨hmt, hLin⟩)
  obtain ⟨hb0, hb1, hpi0, hpi1, -, -⟩ := hk.mem rd hLin
  obtain ⟨rW0, rW1, rPi0, rPi1, -⟩ := hk.reg
  have hsp := hspm rd hmo
  -- the block
  have hV := l5_core (rd := rd) (c := c) (N := gen ^ nk) (written := gen ^ W) (lxt := lxt)
    (cover := cover) (lxs := lxs) (lst := lst) (lss := lss) (carried := gen ^ Cr) (roots := gen ^ R)
    (dcov := gen ^ C) (dslots := gen ^ n) (s0 := s0) (s1 := s1) (cpi := gen ^ Pi) (glp := glp)
    (gsq := gsq) (cfresh := cfresh) (P1 := P1) (d0 := k.dl.1) (d1 := k.dl.2)
    (p0 := (k.pi s0 s1).1) (p1 := (k.pi s0 s1).2) hlow hk.ex_le hk.es_le hk.ed_le hk.can
    (by rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hb0) (hsp 0 (by simp)) (hsp 1 (by simp))
    (by rw [gen_sq', loadHolds_mul_gen_pow, Nat.add_zero]; exact hpi0)
    (by rw [gen_sq', loadHolds_mul_gen_pow]; exact hpi1)
    (by rw [loadHolds_mul_gen_pow]; exact hb1)
  set args : List E := [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, lss, gen ^ Cr, gen ^ R,
    gen ^ C, gen ^ n, s0, s1, gen ^ Pi, glp, gsq, cfresh] with hargs
  set σ := l5σ rd args (l5W k.ex k.es k.ed P1 k.cx.1 k.cx.2 k.cs.1 k.cs.2 k.dl.1 k.dl.2
    (k.pi s0 s1).1 (k.pi s0 s1).2) with hσ
  have pr : ∀ i (hi : i < 18), σ (.n i) = args.getD i 0 := hV.par
  -- the path
  have hw' := Main.walk_straight σ [] (l5Pre ++ [l5Tail]) l5Pre_straight
  rw [← l5Body_split, l5Body] at hw'
  rw [← l5_body] at hw'
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ l5Pre_straight
  have hal : allocs σ ((l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ)) = [2, 4 * k.ed] := by
    rw [hpa, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.allocSz =
      [(.n 56, .inl 2), (.n 70, .inr (.n 69))] from rfl]
    simp only [List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id, hV.v69,
      logG_gen_pow (show 4 * k.ed < 2 ^ 64 - 1 by have := hk.ed_le; omega)]
  have h72 : decide (σ (.n 72) ≠ 0) = decide (k.ed ≠ 0) := by
    rw [hV.v72]; exact decide_eq_decide.mpr (one_add_ne5 (by have := hk.ed_le; omega))
  have h92 : decide (σ (.n 92) ≠ 0) = decide (c + 1 ≠ nk) := by
    rw [hV.v92]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
      fun h he => h ?_⟩
    exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)
  have hcalls : calls ((l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ)) =
      [⟨"child_claim_list_digest", [.n 3, .n 4, .n 19, .n 31, .n 5, .n 20], [.n 32, .n 33], true⟩,
        ⟨"child_claim_list_digest", [.n 6, .n 4, .n 34, .n 5, .n 7, .n 21], [.n 35, .n 36], true⟩,
        ⟨"__loop28", [.n 73, .n 63, .n 70, .n 9, .n 10, .n 11, .n 19, .n 30], [], decide (k.ed ≠ 0)⟩,
        ⟨"da_list_digest", [.n 70, .n 63], [.n 74, .n 75], true⟩,
        ⟨"statement_digest", [.n 12, .n 13, .n 56, .n 74, .n 75, .n 62], [.n 76, .n 77], true⟩,
        ⟨"verify_sub", [.n 76, .n 77, .n 12, .n 13, .n 15, .n 16, .n 86], [], true⟩] ++
      [⟨"__loop5", [.n 94, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11,
        .n 12, .n 13, .n 14, .n 15, .n 16, .n 17], [], decide (c + 1 ≠ nk)⟩] := by
    rw [hpc, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.callS =
      [(none, "child_claim_list_digest", [.n 3, .n 4, .n 19, .n 31, .n 5, .n 20], [.n 32, .n 33]),
        (none, "child_claim_list_digest", [.n 6, .n 4, .n 34, .n 5, .n 7, .n 21], [.n 35, .n 36]),
        (some (.n 72), "__loop28", [.n 73, .n 63, .n 70, .n 9, .n 10, .n 11, .n 19, .n 30], []),
        (none, "da_list_digest", [.n 70, .n 63], [.n 74, .n 75]),
        (none, "statement_digest", [.n 12, .n 13, .n 56, .n 74, .n 75, .n 62], [.n 76, .n 77]),
        (none, "verify_sub", [.n 76, .n 77, .n 12, .n 13, .n 15, .n 16, .n 86], []),
        (some (.n 92), "__loop5", [.n 94, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9,
          .n 10, .n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17], [])] from rfl]
    simp only [List.map_cons, List.map_nil, Main.mkCall, h72, h92, List.cons_append,
      List.nil_append]
  have hev : ∀ e ∈ (l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ), e.Holds rd σ := by
    refine slEvs_holds fun s hs => ?_
    rcases List.mem_append.mp hs with hs | hs
    · have hk' := List.all_eq_true.mp l5_kinds s hs
      match s, hk' with
      | .atom a, _ => exact hV.atoms a (Da.mem_atomsIn hs)
      | .call .., _ => trivial
      | .callIf c f as, hk' =>
        simp only [l5Kind, decide_eq_true_eq] at hk'
        subst hk'
        show IsInK (σ (.n 72))
        rw [hV.v72, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      | .ite .., hk' => simp [l5Kind] at hk'
      | .match_ .., hk' => simp [l5Kind] at hk'
      | .dispatch .., hk' => simp [l5Kind] at hk'
      | .ret _, hk' => simp [l5Kind] at hk'
    · rw [List.mem_singleton] at hs
      subst hs
      show IsInK (σ (.n 92))
      rw [hV.v92]; exact gen_pow_add_isInK _ _
  have hparams : (coreProgram.getD 37 default).params.map σ = args := by
    rw [l5_params]
    refine List.ext_getElem (by simp [hargs]) fun i h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range]
    rw [pr i (by simpa using h1), List.getD_eq_getElem _ _ h2]
  -- the own data
  have hown : ∀ i, RegionL Own i → ownData cert fp (fp + fs "__loop5" + nt) "__loop5" [2, 4 * k.ed]
      ((l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ)) i :=
    fun i hi => Or.inl (bufL_region _ _ _ hfit i hi)
  have h := relAtInWT_of_walk_loop (P := coreProgram) (Tt := Tt) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (Rt := RegionL Lin) (Dt := RegionL []) (fp := fp)
    (m := nt) (N := Nk) (args := args)
    (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3, o4, o5, o6] i)
    coreProgram_wf find_l5 l5_loop hparams hw' rfl hev hcalls
    (by
      by_cases hlast : c + 1 = nk
      · simpa [hlast] using ht
      · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte] at ht ⊢
        rw [show [V.n 94, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11,
          .n 12, .n 13, .n 14, .n 15, .n 16, .n 17].map σ = [σ (.n 94), σ (.n 1), σ (.n 2),
          σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9), σ (.n 10),
          σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15), σ (.n 16), σ (.n 17)] from rfl,
          hV.v94, pr 1 (by omega), pr 2 (by omega), pr 3 (by omega), pr 4 (by omega),
          pr 5 (by omega), pr 6 (by omega), pr 7 (by omega), pr 8 (by omega), pr 9 (by omega),
          pr 10 (by omega), pr 11 (by omega), pr 12 (by omega), pr 13 (by omega), pr 14 (by omega),
          pr 15 (by omega), pr 16 (by omega), pr 17 (by omega)]
        exact ht)
    (by
      rw [hal, hpd, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.allocSz =
        [(.n 56, .inl 2), (.n 70, .inr (.n 69))] from rfl]
      simp only [List.map_cons, List.map_nil, bases, hV.v56, hV.v70, gen_pow_eq_ofK]
      rfl)
    (fun q hq => by
      rw [hpad, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.addrS = [] from rfl] at hq
      simp at hq)
    ?_ (fun i hi => Or.inl hi) ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · rw [hal] at h
    obtain ⟨t, ht, ks', k', rfl, hk'⟩ := h
    refine ⟨_, ht, σ, _, ks', k', rfl, hV.v20, hV.v21, hV.v63, fun hlt => hk' ?_⟩
    simp only [decide_eq_true_eq]
    omega
  · rw [hal]
    refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun kd hkd _ i hi => ?_)
    · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
        fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
        fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 3), σ (.n 4), σ (.n 19), σ (.n 31), σ (.n 5), σ (.n 20)] = _
        rw [pr 3 (by omega), pr 4 (by omega), hV.v19, hV.v31, pr 5 (by omega), hV.v20]; rfl
      · rw [(h1 rfl).1]; show [σ (.n 32), σ (.n 33)] = _; rw [hV.v32, hV.v33]
      · show [σ (.n 6), σ (.n 4), σ (.n 34), σ (.n 5), σ (.n 7), σ (.n 21)] = _
        rw [pr 6 (by omega), pr 4 (by omega), hV.v34, pr 5 (by omega), pr 7 (by omega), hV.v21]
        rfl
      · rw [(h2 rfl).1]; show [σ (.n 35), σ (.n 36)] = _; rw [hV.v35, hV.v36]
      · show [σ (.n 73), σ (.n 63), σ (.n 70), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 19),
          σ (.n 30)] = _
        rw [hV.v73, hV.v63, hV.v70, pr 9 (by omega), pr 10 (by omega), pr 11 (by omega), hV.v19,
          hV.v30]
        rfl
      · rename_i ht3
        rw [(h3 ht3).1]; rfl
      · show [σ (.n 70), σ (.n 63)] = _; rw [hV.v70, hV.v63]
      · rw [(h4 rfl).1]; show [σ (.n 74), σ (.n 75)] = _; rw [hV.v74, hV.v75]
      · show [σ (.n 12), σ (.n 13), σ (.n 56), σ (.n 74), σ (.n 75), σ (.n 62)] = _
        rw [pr 12 (by omega), pr 13 (by omega), hV.v56, hV.v74, hV.v75, hV.v62]
        rfl
      · rw [(h5 rfl).1]; show [σ (.n 76), σ (.n 77)] = _; rw [hV.v76, hV.v77]
      · show [σ (.n 76), σ (.n 77), σ (.n 12), σ (.n 13), σ (.n 15), σ (.n 16), σ (.n 86)] = _
        rw [hV.v76, hV.v77, pr 12 (by omega), pr 13 (by omega), pr 15 (by omega),
          pr 16 (by omega), hV.v86]
        rfl
      · rw [(h6 rfl).1]; rfl
    · intro q hq
      simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at hq
      rcases hq with hq | hq | (hq | hq) | hq | (hq | hq) | hq
      all_goals first | exact hLin q hq | exact hmo q hq
    · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hkd
      have hR : ∀ i, RegionL Lin i → (RegionL Lin i ∨ ownData cert fp (fp + fs "__loop5" + nt)
          "__loop5" [2, 4 * k.ed] ((l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ)) i) ∨ False :=
        fun i h => Or.inl (Or.inl h)
      have hO : ∀ i, RegionL Own i → (RegionL Lin i ∨ ownData cert fp (fp + fs "__loop5" + nt)
          "__loop5" [2, 4 * k.ed] ((l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ)) i) ∨ False :=
        fun i h => Or.inl (Or.inr (hown i h))
      have hLO : ∀ i, RegionL (Lin ++ Own) i → (RegionL Lin i ∨ ownData cert fp
          (fp + fs "__loop5" + nt) "__loop5" [2, 4 * k.ed]
          ((l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ)) i) ∨ False := by
        rintro i ⟨q, hq, hq1, hq2⟩
        rcases List.mem_append.mp hq with hq | hq
        · exact hR i ⟨q, hq, hq1, hq2⟩
        · exact hO i ⟨q, hq, hq1, hq2⟩
      rcases hkd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hR i hi
      · exact hR i hi
      · exact hLO i hi
      · exact hO i hi
      · exact hLO i hi
      · exact hR i hi
  · intro A hA
    rw [B1.loadAddrs_straight σ _ l5Pre_straight,
      show (l5Pre ++ [l5Tail]).filterMap B1.Stmt.loadS =
        [(.n 18, 0), (.n 56, 0), (.n 56, 1), (.n 79, 0), (.n 80, 1), (.n 89, 1)] from rfl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rw [hal]
    have hW' : ∀ e, (gen ^ W * gen ^ c).limb 0 * gpow e = gpow (W + c + e) := fun e => by
      rw [← pow_add, limb0_gen_pow_mul]
    have hPi' : ∀ e, (gen ^ Pi * (gen ^ c * gen ^ c)).limb 0 * gpow e = gpow (Pi + 2 * c + e) :=
      fun e => by rw [gen_sq', ← pow_add, limb0_gen_pow_mul]
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨W + c + 0, ?_, Or.inr (Or.inl rW0)⟩
      rw [hV.v18]; exact hW' 0
    · refine ⟨P1 + 0, ?_, Or.inl (hown _ ⟨(P1, [k.sp.1, k.sp.2]), mSp, Nat.le_add_right _ _,
        show P1 + 0 < P1 + 2 by omega⟩)⟩
      rw [hV.v56, limb0_gen_pow_mul]
    · refine ⟨P1 + 1, ?_, Or.inl (hown _ ⟨(P1, [k.sp.1, k.sp.2]), mSp, Nat.le_add_right _ _,
        show P1 + 1 < P1 + 2 by omega⟩)⟩
      rw [hV.v56, limb0_gen_pow_mul]
    · refine ⟨Pi + 2 * c + 0, ?_, Or.inr (Or.inl rPi0)⟩
      rw [hV.v79]; exact hPi' 0
    · refine ⟨Pi + 2 * c + 1, ?_, Or.inr (Or.inl rPi1)⟩
      rw [hV.v80]; exact hPi' 1
    · refine ⟨W + c + 1, ?_, Or.inr (Or.inl rW1)⟩
      rw [hV.v89]; exact hW' 1

/-- **`__loop5` is complete, placed, its trees exposed**: `l5_completeAt`, from counter `c`, by
the `nk - c` iterations' nodes holding the children's hinted counts. -/
theorem l5_completeAtT {Lin : Layout} {W Pi Cr R C n nk : ℕ}
    {lxt cover lxs lst lss s0 s1 glp gsq cfresh : E} {kid : ℕ → KidH}
    (hn : n ≤ 2 ^ 16) (hnk : nk < 2 ^ 34) (hs01 : AllCanonical [s0, s1])
    (hk : ∀ c < nk, KidOkC fs cert Lin W Pi Cr R C n lxt cover lxs lst lss s0 s1 glp gsq cfresh c
      (kid c)) :
    ∀ c < nk, CompleteAtDT fs cert 16 "__loop5" Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, lss, gen ^ Cr, gen ^ R, gen ^ C,
        gen ^ n, s0, s1, gen ^ Pi, glp, gsq, cfresh] (Returns [])
      (L5From (fun c => (kid c).ex) (fun c => (kid c).es) (fun c => (kid c).ed) (nk - c) c) := by
  have key : ∀ t c, c + 1 + t = nk → CompleteAtDT fs cert 16 "__loop5" Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, lss, gen ^ Cr, gen ^ R, gen ^ C,
        gen ^ n, s0, s1, gen ^ Pi, glp, gsq, cfresh] (Returns [])
      (L5From (fun c => (kid c).ex) (fun c => (kid c).es) (fun c => (kid c).ed) (t + 1) c) := by
    intro t
    induction t with
    | zero =>
      intro c hc
      refine completeAtDT_mono (l5_stepAtT fs cert (Tt := fun _ => True) hn hnk (by omega) hs01
        (hk c (by omega)) fun h => absurd h (by omega)) fun t ht => ?_
      obtain ⟨σ, bufs, ks, k', rfl, h20, h21, h63, -⟩ := ht
      exact ⟨σ, bufs, ks, k', rfl, h20, h21, h63, fun h => absurd rfl h⟩
    | succ t ih =>
      intro c hc
      refine completeAtDT_mono (l5_stepAtT fs cert hn hnk (by omega) hs01 (hk c (by omega))
        fun _ => ih (c + 1) (by omega)) fun t' ht => ?_
      obtain ⟨σ, bufs, ks, k', rfl, h20, h21, h63, hk'⟩ := ht
      exact ⟨σ, bufs, ks, k', rfl, h20, h21, h63, fun _ => hk' (by omega)⟩
  intro c hc
  rw [show nk - c = nk - c - 1 + 1 by omega]
  exact key (nk - c - 1) c (by omega)

variable {fs cert}

/-- **`main`'s honest children loop is complete, its trees exposed** (`L5Hinted`): under the
hypotheses of `mainGoalL5`. -/
theorem mainGoalL5T {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    {bytecode : List K} (hbl : bytecode.length = 2 ^ bytecodeVars)
    (hrel : NodeRel bytecode seed s w) (hl : Limits bytecode s w)
    (hV : ∀ c (hc : c < w.children.length), CompleteAtD fs cert 16 "verify_sub" (hLmain fs fp seed s w)
      [(digestScalars (statementDigest seed w.children[c].statement)).1,
        (digestScalars (statementDigest seed w.children[c].statement)).2,
        (digestScalars seed).1, (digestScalars seed).2, (hm fs fp seed s w).et1,
        (hm fs fp seed s w).et2, (hm fs fp seed s w).a400 * gen ^ (24 * c)] (Returns [])) :
    MainGoalL5T fs cert fp seed s w (L5Hinted w) := by
  intro hnc
  have hcov := cover_bound hl
  have hnc16 := hl.children
  have h := l5_completeAtT fs cert (Lin := hLmain fs fp seed s w) (W := hP fs fp seed s w 9)
    (Pi := hP fs fp seed s w 6) (Cr := hP fs fp seed s w 8) (R := hP fs fp seed s w 0)
    (C := hP fs fp seed s w 4 + (s.claims.xmss.length + (xPlan s w).dups.length +
      (s.claims.sphincs.length + (sPlan s w).dups.length)))
    (n := s.claims.da.length + (dPlan s w).dups.length) (nk := w.children.length)
    (kid := hKid s w) (by omega) (by omega)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (digestScalars_canonical _).1
      · exact (digestScalars_canonical _).2)
    (fun c hc => kidOk cert hbl hrel hl hV hc) 0 (by have : w.children.length ≠ 0 := hnc; omega)
  rw [show (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd +
      ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd)) = gen ^ (hP fs fp seed s w 4 +
      (s.claims.xmss.length + (xPlan s w).dups.length +
        (s.claims.sphincs.length + (sPlan s w).dups.length))) from (pow_add _ _ _).symm]
  rw [pow_zero, Nat.sub_zero] at h
  exact h

end
end LeanVM.Guest.B1.Main
