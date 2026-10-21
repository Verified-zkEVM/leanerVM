/-
  LeanVM.Guest.B1.Comp.VerifySub.PlacedRoot

  `verify_sub` placed over a completeness model, its tree's node decoding the run and its
  `open_stacked` callee's tree satisfying the opening's decoding predicate.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.Placed
public import LeanVM.Guest.B1.Comp.TreeRoot

/-!
# `verify_sub` placed, its child proof decoded

`Placed.lean`'s `verify_sub_completeAtWC` with the callees' trees composed by predicate
(`TreeRoot.lean`): the dispatched `open_stacked`'s placed completeness over the model in tree
form (`CompleteOpenAtBCT CM … OsQ`: the opening's tree, at the frame pointer it is placed at,
satisfies `OsQ μ r os`, the Whir side's statement that its node and `opening_queries` frames
decode to the openings `os`) carried up to `verify_sub`'s tree (`VsRootTree`): `verify_sub`'s node
valuation `σ` decodes the run (`VsDecodes`), and one of its callees' trees, placed at some `b`,
valid on the opening's call words `vsOpenArgs σ`, `vsOpenRets σ`, satisfies
`OsQ μ r D.os b rd`. Hence, for any opening decoder `wO` reading `D.os` there
(`vsProofOf_eq_proof`), `vsProofOf bytecode rd σ wO = D.proof`.

`CompleteOpenAtBC.toBCT`: the earlier shape is the tree form at `OsQ := True`, so
`verify_sub_completeAtWCT` specializes back to `verify_sub_completeAtWC`'s statement.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The opening in tree form -/

/-- **`open_stacked`, placed, bounded, over the model, its tree satisfying `OsQ`**
(`CompleteOpenAtBC`): at the frame pointer `fp` on the memory `rd` the opening's tree satisfies
`OsQ μ r os fp rd`. The Whir side provides it with `OsQ μ r os fp rd t` saying the tree `t`
(the node of `openName μ r` placed at `fp`, its `opening_queries` frames and their loops) decodes
to the openings `os`. -/
def CompleteOpenAtBCT (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop) (B : ℕ)
    (OsQ : ℕ → ℕ → List Opening → ℕ → Reader → Tree → Prop) : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (root cv : Digest) (xs : List E) (os : List Opening) (w : WhirEnd) (cv' : Digest)
      (roots' : List (Digest × ℕ × ℕ)) (target : E) (c : ℕ) (Lin : Main.Layout),
      RunsWithM CM.hm (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots' →
      CapOk μ r root cv xs os target →
      (∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow c)) xs) →
      CompleteAtBST CM.sem fs cert k (openName μ r) Lin [(digestScalars cv).1, (digestScalars cv).2,
        target, (digestScalars root).1, (digestScalars root).2, ofK (Parameters.gpow c)]
        (fun rets Lout =>
          ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
            Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)]) B (OsQ μ r os)

variable {CM : CompModel} {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ}
  {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop} {B : ℕ}

theorem CompleteOpenAtBCT.toBC {OsQ : ℕ → ℕ → List Opening → ℕ → Reader → Tree → Prop}
    (h : CompleteOpenAtBCT CM fs cert k CapOk B OsQ) : CompleteOpenAtBC CM fs cert k CapOk B := by
  intro μ r h1 h2 h3 h4 root cv xs os w cv' roots' target c Lin hrun hcap hm
  exact (h μ r h1 h2 h3 h4 root cv xs os w cv' roots' target c Lin hrun hcap hm).toBS

theorem CompleteOpenAtBC.toBCT (h : CompleteOpenAtBC CM fs cert k CapOk B) :
    CompleteOpenAtBCT CM fs cert k CapOk B fun _ _ _ _ _ _ => True := by
  intro μ r h1 h2 h3 h4 root cv xs os w cv' roots' target c Lin hrun hcap hm
  exact (h μ r h1 h2 h3 h4 root cv xs os w cv' roots' target c Lin hrun hcap hm).toBST

/-- A tree form's tree is placed at the frame pointer. -/
theorem CompleteAtBST.placed {S : BlakeSem} {κ : ℕ} {f : String} {Lin : Main.Layout} {args : List E}
    {Out : List E → Main.Layout → Prop} {B : ℕ} {Q : ℕ → Reader → Tree → Prop}
    (h : CompleteAtBST S fs cert κ f Lin args Out B Q) :
    CompleteAtBST S fs cert κ f Lin args Out B fun fp rd t => Q fp rd t ∧ t.Placed coreProgram fs cert fp :=
  fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hq, hn', hv, hb, hp, ht, hl', hd'⟩ := hr rd hl hm
    ⟨t, ⟨hq, hp⟩, hn', hv, hb, hp, ht, hl', hd'⟩⟩

/-- **A callee's tree at a call of the path**: the tree `KidsSat` gives at the call `c` after
the calls `cs1`, placed at one of the positions, valid on the call's words. -/
theorem kidsSat_at {S : BlakeSem} {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs1 : List Call} {c : Call} {cs2 : List Call} {qs1 : List (ℕ → Tree → Prop)}
      {q : ℕ → Tree → Prop} {qs2 : List (ℕ → Tree → Prop)} {bs : List ℕ} {ks : List Tree},
      Tree.KidsValidB S P rd σ (cs1 ++ c :: cs2) ks → qs1.length = cs1.length →
      KidsSat (cs1 ++ c :: cs2) (qs1 ++ q :: qs2) bs ks → bs.length = ks.length →
      ∃ k ∈ ks, ∃ b, (c.taken = true → q b k) ∧
        (c.taken = true → k.ValidB S P rd (c.args.map σ) (c.rets.map σ)) ∧ k.name = c.f
  | [], c, cs2, [], q, qs2, b :: bs, k :: ks, hv, _, hs, _ => by
    simp only [List.nil_append, Tree.KidsValidB, KidsSat] at hv hs
    refine ⟨k, List.mem_cons_self, b, hs.1, fun ht => ?_, hv.1⟩
    have := hv.2.1
    rw [ite_eq_left ht] at this
    exact this
  | [], _, _, [], _, _, [], _ :: _, _, _, _, hl => absurd hl (by simp)
  | [], _, _, [], _, _, _, [], hv, _, _, _ => by simp [Tree.KidsValidB] at hv
  | [], _, _, _ :: _, _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _ :: _, _, _, [], _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | c1 :: cs1, c, cs2, q1 :: qs1, q, qs2, b :: bs, k :: ks, hv, hl, hs, hbl => by
    simp only [List.cons_append, Tree.KidsValidB, KidsSat] at hv hs
    obtain ⟨k', hk', b', h1, h2, h3⟩ := kidsSat_at hv.2.2 (by simpa using hl) hs.2 (by simpa using hbl)
    exact ⟨k', List.mem_cons_of_mem _ hk', b', h1, h2, h3⟩
  | _ :: _, _, _, _ :: _, _, _, [], _ :: _, _, _, _, hl => absurd hl (by simp)
  | _ :: _, _, _, _ :: _, _, _, _, [], hv, _, _, _ => by simp [Tree.KidsValidB] at hv

/-- **The opening is complete within weights over the model, its tree satisfying `OsQ`**
(`vsOpenKid_completeWC`), and placed. -/
theorem vsOpenKid_completeWCT {D : VsData} {R : VsRunC} {bytecode : List K} {fp lpA sqA outA : ℕ}
    {κ : ℕ} {OsQ : ℕ → ℕ → List Opening → ℕ → Reader → Tree → Prop} {Θ : Type}
    {w : Θ → String → ℕ} (H : VsWeightHypsS CM.sem w) (hok : D.OkC CM bytecode R)
    (hO : CompleteOpenAtBCT CM fs cert κ CapOk B OsQ)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root R.cvL D.xsW D.os
      (R.target D)) :
    let k := vsOpenKidC fs bytecode D R fp lpA sqA outA
    CompleteAtWST CM.sem fs cert w κ k.f k.Lin k.args k.Out B (fun θ => H.os θ)
      fun b rd t => OsQ (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.os b rd t ∧
        t.Placed coreProgram fs cert b := by
  intro k
  have h := hO _ D.rate hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le D.root R.cvL D.xsW D.os D.w
    D.cvW D.roots' (R.target D) _ (vsAllLC fs D R fp lpA sqA outA) hok.opening hcap fun rd _ hm => by
      have := (stream_at hok.rows_length
        (vsAll_memC (off := 0) (kap := 0) (pt := 0) hm).1.stream).2.2.2
      rwa [curW_eq] at this
  rw [← curW_eq (off := 0) (kap := 0) (pt := 0)] at h
  exact CompleteAtBST.toWST_weightLe (CompleteAtBST.placed h) fun θ =>
    H.os_le θ _ _ hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le

/-! ## `verify_sub`'s tree -/

/-- **`verify_sub`'s tree decodes the run**: the node of `verify_sub` whose valuation decodes the
run (`VsDecodes`), one of its callees' trees, placed at `b`, valid on the opening's call words,
satisfying the opening's predicate at the run's configuration and openings. -/
def VsRootTree (S : BlakeSem) (OsQ : ℕ → ℕ → List Opening → ℕ → Reader → Tree → Prop)
    (bytecode : List K) (D : VsData) (R : VsRunC) (fs : String → ℕ) (cert : String → V → ℕ)
    (fp : ℕ) (rd : Reader) (t : Tree) : Prop :=
  ∃ (σ : Val) (bufs : List ℕ) (ks : List Tree), t = Memory.Tree.node "verify_sub" σ bufs ks ∧
    VsDecodes bytecode D R fs fp rd σ ∧ ∃ ko ∈ ks, ∃ b : ℕ,
      OsQ (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.os b rd ko ∧
      ko.Placed coreProgram fs cert b ∧ ko.ValidB S coreProgram rd (vsOpenArgs σ) (vsOpenRets σ)

/-- **The child proof `verify_sub`'s frame decodes is the run's**, for an opening decoder reading
the run's openings on the opening's call. -/
theorem vsProofOf_eq_proof {bytecode : List K} {D : VsData} {R : VsRunC} {fp : ℕ} {rd : Reader}
    {σ : Val} (h : VsDecodes bytecode D R fs fp rd σ) (wO : String → List E → List E → List Opening)
    (hO : wO (openName (vsLayout bytecode σ).stackLog (vsRate σ)) (vsOpenArgs σ) (vsOpenRets σ) = D.os) :
    vsProofOf bytecode rd σ wO = D.proof := by
  simp only [vsProofOf, h.stream, VsData.proof, hO]

variable {bytecode : List K} {D : VsData} {R : VsRunC}

/-- **`verify_sub` is complete over the model, its tree decoding the run**
(`verify_sub_completeAtWC`): the opening's tree form carried up (`VsRootTree`). -/
theorem verify_sub_completeAtWCT {κ : ℕ} (hκ : 7 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {OsQ : ℕ → ℕ → List Opening → ℕ → Reader → Tree → Prop}
    {Θ : Type} {w : Θ → String → ℕ} (H : VsWeightHypsS CM.sem w) {Bsw : VsBoundsW Θ}
    {Bs : VsBounds} (hG : CompleteGkrAtWC CM fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtWC CM fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtWC CM fs cert κ w Bs.fl Bsw.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl)
    (hO : CompleteOpenAtBCT CM fs cert κ CapOk Bs.op OsQ)
    (hE : CompleteTermAtW fs cert κ TCtx PCtx w Bs.term Bsw.term)
    (hb : bytecode.length = 2 ^ 22) (hR : R.Ans CM D) (hok : D.OkC CM bytecode R)
    (htok : D.TOk bytecode)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root R.cvL D.xsW D.os
      (R.target D))
    (lpA sqA outA : ℕ) :
    CompleteAtWST CM.sem fs cert w κ "verify_sub" (vsExtLC lpA sqA outA D R)
      [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
        (digestScalars D.seed).2, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA),
        ofK (Parameters.gpow outA)] (Returns []) (vsBound fs Bs) (fun θ => vsBoundWS w H Bsw θ)
      fun fp rd t => VsRootTree CM.sem OsQ bytecode D R fs cert fp rd t := by
  intro fp
  have hfit := vsBufs_fitC hok htok
  -- the calls before the dispatch
  obtain ⟨N1, L1, outs1, ho1, hw1, hd1, hb1, hi1, hK1⟩ :=
    kidsFromInWST_of_kidsBW κ (vsBd fs Bs) (vsBdWS w H Bsw) (fun _ _ _ _ => True)
    (vsKids1C fs D R fp lpA sqA outA)
    (fun k hk ht => CompleteAtWS.toWST (vsKids1_completeWC hb hok htok H hG hT hF hPl hκ k hk ht))
    (fp + fs "verify_sub" + (vsSizes D).sum)
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, rfl⟩ :=
    list12 (ho1.length.trans (by simp [vsKids1C]))
  have h10 : PlaceOut D o10.1 o10.2 := by
    simp only [OutsOk, vsKids1C, forall_const] at ho1
    exact ho1.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨off, kap, hr10, hpc⟩ := h10
  -- the opening
  obtain ⟨N2, L2, outs2, ho2, hw2, hd2, hb2, hi2, hK2⟩ :=
    kidsFromInWST_of_kidsBW κ (fun _ => Bs.op) (fun _ θ => H.os θ) (fun _ => (fun b rd t => OsQ (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.os b rd t ∧
        t.Placed coreProgram fs cert b))
    [vsOpenKidC fs bytecode D R fp lpA sqA outA] (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk; exact vsOpenKid_completeWCT H hok hO hcap)
    (fp + fs "verify_sub" + (vsSizes D).sum + N1)
  obtain ⟨oO, rfl⟩ := list1 (ho2.length.trans rfl)
  have hoO : OpenOutK D oO.1 oO.2 := by simpa [OutsOk, vsOpenKidC] using ho2
  obtain ⟨bp, hr2, hLo⟩ := hoO
  set ptw := D.w.point ++ List.replicate (pointCap - D.w.point.length) 0
  -- the terminal
  obtain ⟨N3, L3, outs3, ho3, hw3, hd3, hb3, hi3, hK3⟩ :=
    kidsFromInWST_of_kidsBW κ (fun _ => Bs.term) (fun _ => Bsw.term) (fun _ _ _ _ => True)
    [vsTermKidC fs D R fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]]
    (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk
      exact CompleteAtWS.toWST (vsTermKid_completeWC hb hok htok hE hpc))
    (fp + fs "verify_sub" + (vsSizes D).sum + N1 + N2)
  obtain ⟨oT, rfl⟩ := list1 (ho3.length.trans rfl)
  have hoT : oT.1 = [] := by
    have := ho3; simp only [OutsOk, vsTermKidC, Returns, forall_const] at this; exact this.1.1
  refine ⟨fs "verify_sub" + (vsSizes D).sum + (N1 + (N2 + N3)),
    vsOwnLC fs fp D R ++ (L1 ++ (L2 ++ L3)), [], [], ⟨rfl, rfl⟩, ?_, ?_, ?_, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    refine ⟨(bufL_within _ _ _ hfit).mono (by omega) (by omega), hw1.mono (by omega) (by omega),
      hw2.mono (by omega) (by omega), hw3.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    have w23 : Within (L2 ++ L3) (fp + fs "verify_sub" + (vsSizes D).sum + N1) (N2 + N3) :=
      within_append.mpr ⟨hw2.mono le_rfl (by omega), hw3.mono (by omega) (by omega)⟩
    have w123 : Within (L1 ++ (L2 ++ L3)) (fp + fs "verify_sub" + (vsSizes D).sum)
        (N1 + (N2 + N3)) :=
      within_append.mpr ⟨hw1.mono le_rfl (by omega), w23.mono (by omega) (by omega)⟩
    exact disj_append (bufL_disj _ _ _ hfit)
      (disj_append hd1 (disj_append hd2 hd3 hw2 hw3 le_rfl) hw1 w23 le_rfl)
      (bufL_within _ _ _ hfit) w123 le_rfl
  · have := vsSizes_leC hok
    have := vsKids1_boundC (fs := fs) (D := D) (R := R) (fp := fp) (lpA := lpA) (sqA := sqA)
      (outA := outA) Bs
    simp only [kidsBound, vsOpenKidC, vsTermKidC, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, ↓reduceIte] at hb2 hb3
    unfold vsBound
    omega
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLe⟩ := Main.memL_append.mp hL
  obtain ⟨hOwn, hLs⟩ := Main.memL_append.mp hLm
  obtain ⟨hL1, hL23⟩ := Main.memL_append.mp hLs
  obtain ⟨hL2, hL3⟩ := Main.memL_append.mp hL23
  have hAll : MemL rd (vsAllLC fs D R fp lpA sqA outA) := Main.memL_append.mpr ⟨hOwn, hLe⟩
  obtain ⟨hm0, ht, -, -⟩ := vsAll_memC (off := off) (kap := kap) (pt := ofK (Parameters.gpow bp)) hAll
  obtain ⟨σ, sel, hsel, hfix, hpar, hw, hev, hbody⟩ :=
    vs_runC (bytecode := bytecode) (hlow.mono (by omega)) hb hR hok ht hm0
  obtain ⟨hcs, hcall⟩ := vs_callsC hev
  obtain ⟨hal, hbuf⟩ := vs_allocsC hb hok hfix sel
  have hR' : ∀ i, RegionL (vsAllLC fs D R fp lpA sqA outA) i → RegionL (vsExtLC lpA sqA outA D R) i ∨
      ownData cert fp (fp + fs "verify_sub") "verify_sub" (vsSizes D) (vsEvs σ sel) i := by
    intro i ⟨q, hq, h1, h2⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inr (Or.inl (bufL_region _ _ _ hfit i ⟨q, hq, h1, h2⟩))
    · exact Or.inl ⟨q, hq, h1, h2⟩
  have hc : ∀ c ∈ calls (vsEvs σ sel), c.taken = true →
      (c.f, c.args.map σ, c.rets.map σ) ∈ vsTriplesC bytecode D R
        (vsPtrsAt fs fp D off kap (ofK (Parameters.gpow bp))) (ofK (Parameters.gpow lpA))
        (ofK (Parameters.gpow sqA)) := hcall
  rw [hcs] at hc
  have hTo := hc _ (List.mem_append_right _ List.mem_cons_self) rfl
  have hdec : VsDecodes bytecode D R fs fp rd σ := by
    have hT' := hTo
    vs_decC hT'
    simp only [vsPtrsAt] at hT'
    exact vsDecodes_of hok hfix hbody hm0 (by simp only [hT']) ⟨bp, rfl⟩
  have h := relAtInWST_of_walk (S := CM.sem) (fs := fs) (cert := cert) (w := w)
    (R := RegionL (vsExtLC lpA sqA outA D R)) (D := RegionL []) (Dk := fun _ => False)
    (N := N1 + (N2 + N3)) (fp := fp)
    (bws := Main.kidsWs (vsBdWS w H Bsw) (vsKids1C fs D R fp lpA sqA outA) ++
      (Main.kidsWs (fun _ θ => H.os θ) [vsOpenKidC fs bytecode D R fp lpA sqA outA] ++
        Main.kidsWs (fun _ => Bsw.term)
          [vsTermKidC fs D R fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]]))
    (qs := (vsKids1C fs D R fp lpA sqA outA).map (fun _ _ _ => True) ++
      ([vsOpenKidC fs bytecode D R fp lpA sqA outA].map (fun _ b t => OsQ (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.os b rd t ∧
        t.Placed coreProgram fs cert b) ++
        [vsTermKidC fs D R fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]].map
          (fun _ _ _ => True)))
    (Q := VsRootTree CM.sem OsQ bytecode D R fs cert fp rd)
    find_verify_sub (Or.inl vs_not_loop) hpar hw
    rfl (fun e he => (hev e he).1) (by rw [hal]; exact hbuf)
    (by rw [(vs_parts σ sel).2.2.1]; simp) ?_ ?_ (fun i ⟨q, hq, _⟩ => by simp at hq) ?_
  · rw [hal] at h
    obtain ⟨t, hQ, hn, hv, hbo, hp, htot, hl, hd, hwt⟩ := h
    refine ⟨t, hQ, hn, hv, hbo, hp, htot, hl, hd, fun θ => (hwt θ).trans ?_⟩
    have := vsKids1_boundWC (fs := fs) (D := D) (R := R) (fp := fp) (lpA := lpA) (sqA := sqA)
      (outA := outA) w H Bsw θ
    simp only [List.map_append, List.sum_append, Main.kidsWs_sum]
    have e2 : Main.kidsBoundW (fun _ θ => H.os θ) [vsOpenKidC fs bytecode D R fp lpA sqA outA] θ =
        H.os θ := by
      simp [Main.kidsBoundW, vsOpenKidC]
    have e3 : Main.kidsBoundW (fun _ => Bsw.term)
        [vsTermKidC fs D R fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]] θ =
          Bsw.term θ := by
      simp [Main.kidsBoundW, vsTermKidC]
    rw [e2, e3]
    unfold vsBoundWS
    omega
  · rw [hal, hcs]
    have hm1 := match1C hok hfix (fun c hc' ht' => hc c (List.mem_append_left _ hc') ht') ho1
      (by simpa using hr10)
    refine kidsFromInWST_append _ _ _ _ _ _ _ _ _ _ _ _
      (by rw [Main.kidsWs_length]; exact (Main.callsMatch_length hm1).symm)
      (by rw [List.length_map]; exact (Main.callsMatch_length hm1).symm) (hK1 rd σ _ _ (fun _ => False)
      hm1 (hlow) hL1 (memL_lins ?_) (regionsOk_of ?_))
      fun Dacc' hD1 => kidsFromInWST_append [_] [_] _ _ _ _ _ _ _ _ _ _ rfl rfl (hK2 rd σ _ _ Dacc'
        (matchOpenC hTo hr2) hlow hL2
        (memL_lins ?_) (regionsOk_of ?_))
        fun Dacc'' hD2 => kidsFromInWST_dend _ _ _ _ _ _ (fun _ h => h.elim) (hK3 rd σ _ _ Dacc''
          (matchTermC (hc _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
            rfl) hoT) hlow hL3 (memL_lins ?_) (regionsOk_of ?_))
    · intro k hk
      simp only [vsKids1C, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact gpwSq_memC hAll | exact hAll | exact fun _ h => (List.not_mem_nil h).elim
    · intro k hk ht' i hi
      simp only [vsKids1C, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact Or.inl (hR' i hi)
        | exact absurd hi (fun ⟨_, hq, _⟩ => List.not_mem_nil hq)
        | (obtain ⟨q, hq, h1, h2⟩ := hi
           simp only [List.mem_singleton] at hq
           subst hq
           exact Or.inl (Or.inl ⟨(sqA, (List.range sizeBits).map fun j => gen ^ 2 ^ j),
             by simp [vsExtLC, expL], h1, by simp [gpwSq, sizeBits] at h2 ⊢; omega⟩))
    · intro k hk; rw [List.mem_singleton] at hk; subst hk; exact hAll
    · intro k hk _ i hi; rw [List.mem_singleton] at hk; subst hk; exact Or.inl (hR' i hi)
    · intro k hk; rw [List.mem_singleton] at hk; subst hk
      simp only [OutsIn, vsKids1C, forall_const] at hi1
      simp only [OutsIn] at hi2
      have hc10 := hi1.2.2.2.2.2.2.2.2.2.2.1
      refine Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨hAll, fun q hq => hL1 q (hc10 q hq)⟩,
        fun q hq => hL2 q (hi2.1 rfl q (by rw [hLo]; exact hq))⟩
    · intro k hk _ i hi; rw [List.mem_singleton] at hk; subst hk
      obtain ⟨q, hq, h1, h2⟩ := hi
      simp only [vsTermKidC, List.mem_append] at hq
      rcases hq with (hq | hq) | hq
      · exact Or.inl (hR' i ⟨q, hq, h1, h2⟩)
      · refine Or.inr (hD2 i (Or.inl (hD1 i (Or.inr ?_))))
        simp only [outRegion, vsKids1C]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨trivial, q, hq, h1, h2⟩))))))))))
      · refine Or.inr (hD2 i (Or.inr ?_))
        simp only [outRegion, vsOpenKidC]
        exact Or.inl ⟨trivial, q, by rw [hLo]; exact hq, h1, h2⟩
  · intro A hA
    rw [(vs_parts σ sel).2.2.2.2, List.mem_append] at hA
    have hq : ∃ q, loadOkB q = true ∧ A = (σ q.1).limb 0 * Parameters.gpow q.2 := by
      rcases hA with hA | hA <;> obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      · exact ⟨q, List.all_eq_true.mp vsPre1_loads q hq, rfl⟩
      · exact ⟨q, List.all_eq_true.mp vsPost2_loads q hq, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hq
    obtain ⟨i, hi, h⟩ := vs_loadC hb hok hfix q hq
    refine ⟨i, hi, ?_⟩
    rw [hal]
    rcases h with h | h
    · exact Or.inl (Or.inl (inBuf_own h))
    · exact Or.inr (Or.inl h)
  · intro ks hkv hkq
    rw [hcs] at hkv hkq
    obtain ⟨ko, hko, b, hq, hv, -⟩ := kidsSat_at (qs1 := (vsKids1C fs D R fp lpA sqA outA).map
      (fun _ _ _ => True)) hkv (by simp [vsKids1C, vsPre1_calls]) (by simpa using hkq)
      (by simp [length_bases])
    exact ⟨σ, _, ks, rfl, hdec, ko, hko, b, (hq rfl).1, (hq rfl).2,
      by simpa [vsOpenArgs, vsOpenRets] using hv rfl⟩

/-- `verify_sub_completeAtWCT`, the tree forgotten. -/
theorem verify_sub_completeAtWCT_toWS {κ : ℕ} (hκ : 7 ≤ κ)
    {OsQ : ℕ → ℕ → List Opening → ℕ → Reader → Tree → Prop}
    {Θ : Type} {w : Θ → String → ℕ} (H : VsWeightHypsS CM.sem w) {Bsw : VsBoundsW Θ}
    {Bs : VsBounds} (hG : CompleteGkrAtWC CM fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtWC CM fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtWC CM fs cert κ w Bs.fl Bsw.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl)
    (hO : CompleteOpenAtBCT CM fs cert κ CapOk Bs.op OsQ)
    (hE : CompleteTermAtW fs cert κ TCtx PCtx w Bs.term Bsw.term)
    (hb : bytecode.length = 2 ^ 22) (hR : R.Ans CM D) (hok : D.OkC CM bytecode R)
    (htok : D.TOk bytecode)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root R.cvL D.xsW D.os
      (R.target D))
    (lpA sqA outA : ℕ) :
    Main.CompleteAtWS CM.sem fs cert w κ "verify_sub" (vsExtLC lpA sqA outA D R)
      [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
        (digestScalars D.seed).2, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA),
        ofK (Parameters.gpow outA)] (Returns []) (vsBound fs Bs) fun θ => vsBoundWS w H Bsw θ :=
  (verify_sub_completeAtWCT hκ H hG hT hF hPl hO hE hb hR hok htok hcap lpA sqA outA).toWS

/-- **The deployed `verify_sub` placed, its tree decoding the run**, at any opening tree form at
`CompModel.deployed` (`OsQ := True` from the deployed `CompleteOpenAtB`). -/
theorem verify_sub_completeAtWT_of_comp {κ : ℕ} (hκ : 7 ≤ κ)
    {OsQ : ℕ → ℕ → List Opening → ℕ → Reader → Tree → Prop}
    {Θ : Type} {w : Θ → String → ℕ} (H : VsWeightHyps w) {Bsw : VsBoundsW Θ}
    {Bs : VsBounds} (hG : CompleteGkrAtW fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtW fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtW fs cert κ w Bs.fl Bsw.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl)
    (hO : CompleteOpenAtBCT CompModel.deployed fs cert κ CapOk Bs.op OsQ)
    (hE : CompleteTermAtW fs cert κ TCtx PCtx w Bs.term Bsw.term)
    (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (htok : D.TOk bytecode)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os
      D.target)
    (lpA sqA outA : ℕ) :
    CompleteAtWST blakeDeployed fs cert w κ "verify_sub" (vsExtL lpA sqA outA D)
      [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
        (digestScalars D.seed).2, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA),
        ofK (Parameters.gpow outA)] (Returns []) (vsBound fs Bs) (fun θ => vsBoundW w H Bsw θ)
      fun fp rd t => VsRootTree blakeDeployed OsQ bytecode D (VsRunC.ofD D) fs cert fp rd t := by
  have h := verify_sub_completeAtWCT (CM := CompModel.deployed) hκ H.toS hG.toC hT.toC hF.toC hPl
    hO hE hb (VsRunC.ans_ofD D) hok.toOkC htok
    (by rw [VsRunC.cvL_ofD, VsRunC.target_ofD]; exact hcap) lpA sqA outA
  rw [vsExtLC_ofD] at h
  exact h

end
end LeanVM.Guest.B1.VerifySub
