/-
  LeanVM.Guest.B1.Comp.VerifySub.PlacedEqO

  `verify_sub` placed over a completeness model, its tree decoding the child proof, the opening's
  tree located at the dispatch: its index among the callees and the call it is placed at.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.PlacedEq

/-!
# `verify_sub`'s opening at its dispatch

`VsRootTreeEO`: `VsRootTreeE` with the opening's tree `ko` at index `i` of the callees, the path's
call `i` the dispatched `openName (vsLayout bytecode σ).stackLog (vsRate σ)` on the opening's
call words, its cursor word in `verify_sub`'s own region. `verify_sub_completeAtWCEO`:
`verify_sub_completeAtWCE` by such a tree.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **`VsRootTreeE` with the opening located at the dispatch.** -/
def VsRootTreeEO (S : BlakeSem) (OsQ : ℕ → ℕ → List Opening → ℕ → Tree → Prop)
    (bytecode : List K) (D : VsData) (R : VsRunC) (fs : String → ℕ) (cert : String → V → ℕ)
    (fp : ℕ) (t : Tree) : Prop :=
  ∃ (σ : Val) (bufs : List ℕ) (ks : List Tree), t = Memory.Tree.node "verify_sub" σ bufs ks ∧
    VsFrame bytecode D R fs fp σ ∧
    (∀ rd' : Reader, (∀ q ∈ t.loadEqns coreProgram, rd' q.1 = some q.2) →
      streamAt rd' (σ (.n 14)) (vsStreamLen bytecode σ) = D.stream) ∧
    (∃ a, (vsOpenArgs σ)[5]? = some (ofK (Parameters.gpow a)) ∧ fp ≤ a ∧ a < fp + t.total fs) ∧
    ∃ ko ∈ ks, ∃ b : ℕ, OsQ (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.os b ko ∧
      ko.Placed coreProgram fs cert b ∧
      (∀ rd' : Reader, (∀ q ∈ t.eqns coreProgram, rd' q.1 = some q.2) →
        ko.ValidB S coreProgram rd' (vsOpenArgs σ) (vsOpenRets σ)) ∧
      ∃ (i sel : ℕ), ks[i]? = some ko ∧ walk σ (Fn.body Data.core15) = .ret (vsEvs σ sel) [] ∧
        (calls (vsEvs σ sel))[i]? = some ⟨openName (vsLayout bytecode σ).stackLog (vsRate σ),
          [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726], [.n 1648, .n 1649, .n 1650, .n 1651], true⟩

theorem VsRootTreeEO.toE {S : BlakeSem} {OsQ : ℕ → ℕ → List Opening → ℕ → Tree → Prop} {bytecode : List K}
    {D : VsData} {R : VsRunC} {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {t : Tree}
    (h : VsRootTreeEO S OsQ bytecode D R fs cert fp t) : VsRootTreeE S OsQ bytecode D R fs cert fp t :=
  let ⟨σ, bufs, ks, ht, hf, hs, _, ko, hko, b, hq, hp, hv, _⟩ := h
  ⟨σ, bufs, ks, ht, hf, hs, ko, hko, b, hq, hp, hv⟩

/-- `kidsSat_at` with the callee's index. -/
theorem kidsSat_atI {S : BlakeSem} {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs1 : List Call} {c : Call} {cs2 : List Call} {qs1 : List (ℕ → Tree → Prop)}
      {q : ℕ → Tree → Prop} {qs2 : List (ℕ → Tree → Prop)} {bs : List ℕ} {ks : List Tree},
      Tree.KidsValidB S P rd σ (cs1 ++ c :: cs2) ks → qs1.length = cs1.length →
      KidsSat (cs1 ++ c :: cs2) (qs1 ++ q :: qs2) bs ks → bs.length = ks.length →
      ∃ k ∈ ks, ks[cs1.length]? = some k ∧ ∃ b, (c.taken = true → q b k) ∧
        (c.taken = true → k.ValidB S P rd (c.args.map σ) (c.rets.map σ)) ∧ k.name = c.f
  | [], c, cs2, [], q, qs2, b :: bs, k :: ks, hv, _, hs, _ => by
    simp only [List.nil_append, Tree.KidsValidB, KidsSat] at hv hs
    refine ⟨k, List.mem_cons_self, rfl, b, hs.1, fun ht => ?_, hv.1⟩
    have := hv.2.1
    rw [ite_eq_left ht] at this
    exact this
  | [], _, _, [], _, _, [], _ :: _, _, _, _, hl => absurd hl (by simp)
  | [], _, _, [], _, _, _, [], hv, _, _, _ => by simp [Tree.KidsValidB] at hv
  | [], _, _, _ :: _, _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _ :: _, _, _, [], _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | c1 :: cs1, c, cs2, q1 :: qs1, q, qs2, b :: bs, k :: ks, hv, hl, hs, hbl => by
    simp only [List.cons_append, Tree.KidsValidB, KidsSat] at hv hs
    obtain ⟨k', hk', hi, b', h1, h2, h3⟩ := kidsSat_atI hv.2.2 (by simpa using hl) hs.2 (by simpa using hbl)
    exact ⟨k', List.mem_cons_of_mem _ hk', by simpa using hi, b', h1, h2, h3⟩
  | _ :: _, _, _, _ :: _, _, _, [], _ :: _, _, _, _, hl => absurd hl (by simp)
  | _ :: _, _, _, _ :: _, _, _, _, [], hv, _, _, _ => by simp [Tree.KidsValidB] at hv

/-- **`vsRootTreeE_of` with the opening located at the dispatch.** -/
theorem vsRootTreeEO_of {S : BlakeSem} {C : CallRel} {OsQ : ℕ → ℕ → List Opening → ℕ → Tree → Prop}
    {CM : CompModel} {bytecode : List K} {D : VsData} {R : VsRunC} {fs : String → ℕ}
    {cert : String → V → ℕ} {fp : ℕ} {rd : Reader} {σ : Val} {sel : ℕ} {bufs : List ℕ}
    {ks : List Tree} (hok : D.OkC CM bytecode R)
    (hw : walk σ (Fn.body Data.core15) = .ret (vsEvs σ sel) [])
    (hev : ∀ e ∈ vsEvs σ sel, e.OkB S C rd σ) (hdec : VsDecodes bytecode D R fs fp rd σ)
    (h14 : σ (.n 14) = ofK (Parameters.gpow (vsB fs fp D 2)))
    (hs : ReadsAt rd (σ (.n 14)) D.stream)
    {kG kT kF ko : Tree} (hkG : kG ∈ ks) (hG : LoadsWords kG (vsB fs fp D 2 + 10) D.xsG)
    (hkT : kT ∈ ks) (hT : LoadsWords kT (vsB fs fp D 2 + 10 + D.xsG.length) D.xsT)
    (hkF : kF ∈ ks) (hF : LoadsWords kF (vsB fs fp D 2 + 10 + D.xsG.length + D.xsT.length) D.xsF)
    (hko : ko ∈ ks) {b : ℕ} (hW : LoadsWords ko (vsCurW fs fp D) D.xsW)
    (hq : OsQ (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.os b ko)
    (hp : ko.Placed coreProgram fs cert b)
    (hv : ko.ValidB S coreProgram rd (vsOpenArgs σ) (vsOpenRets σ)) {i : ℕ} (hi : ks[i]? = some ko)
    (hci : (calls (vsEvs σ sel))[i]? = some ⟨openName (vsLayout bytecode σ).stackLog (vsRate σ),
      [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726], [.n 1648, .n 1649, .n 1650, .n 1651], true⟩)
    (hbufs : bufs = vsSizes D) (hst : D.stream.length ≤ 8192) :
    VsRootTreeEO S OsQ bytecode D R fs cert fp (Memory.Tree.node "verify_sub" σ bufs ks) := by
  obtain ⟨σ', bufs', ks', ht, hf, hst', -⟩ := vsRootTreeE_of (OsQ := OsQ) (cert := cert) (bufs := bufs) hok hw hev hdec h14 hs
    hkG hG hkT hT hkF hF hko hW hq hp hv
  simp only [Memory.Tree.node.injEq] at ht
  obtain ⟨-, rfl, rfl, rfl⟩ := ht
  have hE : (Memory.Tree.node "verify_sub" σ bufs ks).eqns coreProgram =
      evEqns σ (vsEvs σ sel) ++ Tree.eqnsKids coreProgram ks := eqns_node find_verify_sub hw
  have hsl : D.stream.length = 10 + D.xsG.length + D.xsT.length + D.xsF.length + D.xsW.length := by
    simp [VsData.stream, VsData.tail, ann_length hok.rows_length]; omega
  have hB2 : vsB fs fp D 2 = fp + fs "verify_sub" + 224 := by
    simp [vsB, vsBases, vsSizes, bases]
  have hcur : ∃ a, (vsOpenArgs σ)[5]? = some (ofK (Parameters.gpow a)) ∧ fp ≤ a ∧
      a < fp + (Memory.Tree.node "verify_sub" σ bufs ks).total fs := by
    refine ⟨vsB fs fp D 2 + 10 + D.xsG.length + D.xsT.length + D.xsF.length, ?_, by omega, ?_⟩
    · rw [hf.openArgs]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
      rw [curW_eq]
      rfl
    · rw [total_node, hbufs]
      have : 224 + 8192 + 6 ≤ (vsSizes D).sum := by simp [vsSizes]; omega
      omega
  refine ⟨σ, bufs, ks, rfl, hf, hst', hcur, ko, hko, b, hq, hp, fun rd' he =>
    Tree.ValidB.transfer ko hv fun q hq' => he q (by rw [hE]; exact List.mem_append_right _ (eqns_of_mem_kids hko q hq')),
    i, sel, hi, hw, hci⟩

variable {fs : String → ℕ} {cert : String → V → ℕ} {bytecode : List K} {D : VsData} {R : VsRunC}
  {CM : CompModel}

/-- **`verify_sub` is complete over the model, its tree decoding the run on its equations**
(`verify_sub_completeAtWCT`): the transcript callees loading the words they read
(`CompleteGkrAtWCL`, `CompleteTablesAtWCL`, `CompleteFlockAtWCL`, `CompleteOpenAtBCL`). -/
theorem verify_sub_completeAtWCEO {κ : ℕ} (hκ : 7 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {OsQ : ℕ → ℕ → List Opening → ℕ → Tree → Prop}
    {Θ : Type} {w : Θ → String → ℕ} (H : VsWeightHypsS CM.sem w) {Bsw : VsBoundsW Θ}
    {Bs : VsBounds} (hG : CompleteGkrAtWCL CM fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtWCL CM fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtWCL CM fs cert κ w Bs.fl Bsw.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl)
    (hO : CompleteOpenAtBCL CM fs cert κ CapOk Bs.op OsQ)
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
      fun fp _ t => VsRootTreeEO CM.sem OsQ bytecode D R fs cert fp t := by
  intro fp
  have hfit := vsBufs_fitC hok htok
  -- the calls before the dispatch
  obtain ⟨N1, L1, outs1, ho1, hw1, hd1, hb1, hi1, hK1⟩ :=
    kidsFromInWST_of_kidsBW κ (vsBd fs Bs) (vsBdWS w H Bsw) (VsKidsQ fs fp D)
    (vsKids1C fs D R fp lpA sqA outA) (vsKids1_completeWCL hb hok htok H hG hT hF hPl hκ)
    (fp + fs "verify_sub" + (vsSizes D).sum)
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, rfl⟩ :=
    list12 (ho1.length.trans (by simp [vsKids1C]))
  have h10 : PlaceOut D o10.1 o10.2 := by
    simp only [OutsOk, vsKids1C, forall_const] at ho1
    exact ho1.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨off, kap, hr10, hpc⟩ := h10
  -- the opening
  obtain ⟨N2, L2, outs2, ho2, hw2, hd2, hb2, hi2, hK2⟩ :=
    kidsFromInWST_of_kidsBW κ (fun _ => Bs.op) (fun _ θ => H.os θ) (fun _ b _ t => (LoadsWords t (vsCurW fs fp D) D.xsW ∧
        OsQ (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.os b t) ∧
        t.Placed coreProgram fs cert b)
    [vsOpenKidC fs bytecode D R fp lpA sqA outA] (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk; exact vsOpenKid_completeWCL H hok hO hcap)
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
    (qs := (vsKids1C fs D R fp lpA sqA outA).map (fun k b t => VsKidsQ fs fp D k b rd t) ++
      ([vsOpenKidC fs bytecode D R fp lpA sqA outA].map (fun _ b t =>
        (LoadsWords t (vsCurW fs fp D) D.xsW ∧
          OsQ (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.os b t) ∧
          t.Placed coreProgram fs cert b) ++
        [vsTermKidC fs D R fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]].map
          (fun _ _ _ => True)))
    (Q := VsRootTreeEO CM.sem OsQ bytecode D R fs cert fp)
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
    have hcs12 : (calls (vsEvs σ sel))[12]? = some ⟨openNames.getD sel "",
        [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726], [.n 1648, .n 1649, .n 1650, .n 1651], true⟩ := by
      rw [hcs, List.getElem?_append_right (by simp [vsPre1_calls])]
      simp [vsPre1_calls]
    have hname : openNames.getD sel "" = openName (vsLayout bytecode σ).stackLog (vsRate σ) := by
      have hT' := hTo
      vs_decC hT'
      rw [hdec.layout, hdec.rate]
      exact hT'.1
    rw [hname] at hcs12
    rw [hcs] at hkv hkq
    have hlk := kidsValidB_length hkv
    have hcl : ((vsPre1.filterMap Main.Stmt.callS).map (Main.mkCall σ)).length = 12 := by
      simp [vsPre1_calls]
    have hql : ((vsKids1C fs D R fp lpA sqA outA).map
        (fun k b t => VsKidsQ fs fp D k b rd t)).length = 12 := by simp [vsKids1C]
    have get := fun i (hi : i < 12) (ht : (((vsPre1.filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
        _)[i]'(by simp [vsPre1_calls]; omega)).taken = true) =>
      kidsSat_get i hkv hkq (by simp [vsPre1_calls]; omega) (by simp [vsKids1C]; omega)
        (by simp [length_bases, ← hlk, vsPre1_calls]; omega) ht
    obtain ⟨kG, hkG, hqG, -⟩ := get 5 (by omega) (by simp [vsPre1_calls, Main.mkCall])
    obtain ⟨kT, hkT, hqT, -⟩ := get 6 (by omega) (by simp [vsPre1_calls, Main.mkCall])
    obtain ⟨kF, hkF, hqF, -⟩ := get 7 (by omega) (by simp [vsPre1_calls, Main.mkCall])
    rw [List.getElem_append_left (by rw [hql]; omega), List.getElem_map] at hqG hqT hqF
    obtain ⟨ko, hko, hko12, b, hq, hv, -⟩ := kidsSat_atI (qs1 := (vsKids1C fs D R fp lpA sqA outA).map
      (fun k b t => VsKidsQ fs fp D k b rd t)) hkv (by simp [vsKids1C, vsPre1_calls]) (by simpa using hkq)
      (by simp [length_bases])
    have h14 : σ (.n 14) = ofK (Parameters.gpow (vsB fs fp D 2)) :=
      (hfix.get (k := 14) (e := (vsPtrsAt fs fp D off kap (ofK (Parameters.gpow bp))).stream)
        (by vs_memC)).trans rfl
    exact vsRootTreeEO_of hok hw hev hdec h14 (by rw [h14]; exact hm0.stream) hkG (hqG.1 rfl) hkT
      (hqT.2.1 rfl) hkF (hqF.2.2 rfl) hko (hq rfl).1.1 (hq rfl).1.2 (hq rfl).2
      (by simpa [vsOpenArgs, vsOpenRets] using hv rfl) (by simpa [vsPre1_calls] using hko12) hcs12 hal
      (by have h2 := hfit; simp only [vsBufsC, vsSizes, List.forall₂_cons] at h2; exact h2.2.2.1)

end
end LeanVM.Guest.B1.VerifySub
