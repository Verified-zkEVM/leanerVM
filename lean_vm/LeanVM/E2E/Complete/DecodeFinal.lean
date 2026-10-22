/-
  LeanVM.E2E.Complete.DecodeFinal

  L2's `GuestCompleteModel`, unconditionally, and T6-det without L2.
-/

module

public import LeanVM.E2E.Complete.DecodeOpen
public import LeanVM.E2E.Complete.DecodeAssembly
public import LeanVM.E2E.Complete.TreeLog
public import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsInj

/-!
# `GuestCompleteModel`

`DecodeAssembly.lean`'s assembly with `verify_sub`'s trees locating their openings
(`VsRootTreeEO`, `verify_sub_completeAtWCEO`): `guestCompleteModel_ofO` from the Whir side's
`open_stacked` in tree form and `D3HypO`. D3 (`d3HypO`): the frames name the children's
`verify_sub` instances, their openings' roots and the openings' decoded callees (`frOf`), every
name and argument words naming one frame (the children's argument words, `vsArgsAt_inj`; the
openings' cursors and pointers, in the children's disjoint regions, `loop5Q_vs_disjoint`,
`os_inj`); each opening decodes to the run's openings (`OsDec`, `kidsLink_of_vagree`,
`vagree_honest`), so each child's proof to the run's (`vs_proof_of_inst`).

* `guestCompleteModel : GuestCompleteModel`;
* `idealVerify_complete_det`: T6-det without L2 (`idealVerify_complete''` at `guestCompleteModel`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Node LeanVM.Protocol.LeanIsa
open LeanVM.Guest.B1.Main (calleeBd vsExtLR VsGoodC honestWordsC mainIn mainVal mainRunAt mainIQ MainQ
  calleesAtC_of_open)

@[expose] public section

/-- **`verify_sub` over a completeness model, by trees decoding the child's run, its opening located** (`VsRootTreeEO`). -/
theorem vs_completeTO (CM : CompModel) {OsQ : ℕ → ℕ → List Opening → ℕ → Memory.Tree → Prop}
    (hO : B1.VerifySub.CompleteOpenAtBCL CM B2C.fs B2C.cert 16 (B1.VerifySub.CapAgreesC CM)
      B2C.calleesHyps_b2c.Bop OsQ) :
    ∀ (D : B1.VerifySub.VsData) (R : B1.VerifySub.VsRunC), VsGoodC CM (B1.VerifySub.CapAgreesC CM) D R →
      ∀ lpA sqA outA : ℕ, ∀ {Θ : Type} (w : Θ → String → ℕ) (c : Θ → B1.VerifySub.VsStat),
      (∀ θ, B1.VerifySub.VsStatOkS CM.sem (w θ) (c θ)) →
      B1.CompleteAtWST CM.sem B2C.fs B2C.cert w 16 "verify_sub" (vsExtLR lpA sqA outA D R)
        [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
          (digestScalars D.seed).2, ofK (gpow lpA), ofK (gpow sqA), ofK (gpow outA)] (B1.Returns [])
        (calleeBd B2C.fs B2C.calleesHyps_b2c).vs
        (fun θ => (calleeBd B2C.fs B2C.calleesHyps_b2c).vsW (w θ) (c θ))
        (fun fp _ t => B1.VerifySub.VsRootTreeEO CM.sem OsQ End.bytecode D R B2C.fs B2C.cert fp t) :=
  fun D R hD lpA sqA outA _ w c hc =>
    B1.VerifySub.verify_sub_completeAtWCEO (CM := CM) (fs := B2C.fs) (cert := B2C.cert) (by norm_num)
      (B1.VerifySub.VsWeightHypsS.ofStat c hc)
      (Bsw := ⟨fun θ => B1.VerifySub.vtcGkrBoundW (w θ), fun θ => B1.VerifySub.vtTablesBoundW (w θ),
        fun θ => B1.flockBoundW (w θ), fun θ => B1.termBoundW (w θ)⟩)
      (Bs := B1.Main.calleeVsB B2C.fs B2C.calleesHyps_b2c) (B2C.gkrCL_b2c CM w) (B2C.tablesCL_b2c CM w)
      (B2C.flockCL_b2c CM w)
      (B1.certify_placement_completeAtB B2C.fs B2C.cert (by norm_num))
      hO
      (B1.check_opening_terminal_completeAtW B2C.fs B2C.cert w 16) End.bytecode_length hD.1
      hD.2.1 hD.2.2.1 hD.2.2.2 lpA sqA outA


/-- **What decoding the children's proofs takes** (D3): on the honest memory of `main`'s
re-chosen tree, from `main`'s tree form with `verify_sub`'s trees decoding the children's runs at
`OsQ` and its openings located (`VsRootTreeEO`), frames at which V_I's decoder reads each child's proof. -/
def D3HypO (OsQ : ℕ → ℕ → List Opening → ℕ → Memory.Tree → Prop) : Prop :=
  ∀ (CM : CompModel) (Ht : Compile.Bytes → Digest) (seed : Digest) (s : NodeStatement)
    (w : NodeWitness) (vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC) (hdr : E × E)
    (rd0 : Reader) (T0 : Memory.Tree) (ν : ℕ → String → Val → V → E) (n : ℕ),
    (∀ c, VrP CM Ht seed w c (vr c)) →
    (T0.retemp coreProgram B2C.fs ν 0).name = "main" →
    T0.ValidB CM.sem coreProgram rd0 [] [] →
    MainQ (fun D R b _ t => B1.VerifySub.VsRootTreeEO CM.sem OsQ End.bytecode D R B2C.fs B2C.cert b t) vr
      (CclQP CM.H) (SdQP CM.H) B1.Main.Loop100Q (mainIQ B2C.fs 0 (honestWordsC Ht seed s w)) B2C.fs
      w.children.length 0 (mainVal rd0 (mainRunAt B2C.fs 0 (honestWordsC Ht seed s w))) rd0 T0 →
    HonestAtB CM.sem coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0) B2C.cert
      (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read [] [] →
    runB CM.sem guest (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) n
      Regs.initial = some (Regs.final guest) →
    B1.Main.MemL rd0 (mainIn B2C.fs 0 (honestWordsC Ht seed s w)) →
    B1.Main.mainBase B2C.fs 0 (honestWordsC Ht seed s w) 6 ≤ 2 ^ 32 → w.children.length ≤ 16 →
    (∀ (a : K) (x : E), (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)).read a = some x → x = 0 ∨ rd0 a = some x ∨
          ∃ I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T0, ∃ i, I.Frame B2C.fs i ∧ a = Parameters.gpow i) →
    ∃ fr : Frames, ∀ c (hc : c < w.children.length),
      Located.wVsLB (honestSem hdr (T0.retemp coreProgram B2C.fs ν 0) n) fr
        (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0))
        (vsArgsAt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) c) [] =
        w.children[c].proof


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **L2: the guest's completeness over a completeness model** (`GuestCompleteModel`), from the
Whir side's `open_stacked` in tree form at `OsQ` and the decoding of the children's proofs
(`D3Hyp OsQ`). -/
theorem guestCompleteModel_ofO {OsQ : ℕ → ℕ → List Opening → ℕ → Memory.Tree → Prop}
    (hOpen : ∀ CM : CompModel, B1.VerifySub.CompleteOpenAtBCL CM B2C.fs B2C.cert 16
      (B1.VerifySub.CapAgreesC CM) B2C.calleesHyps_b2c.Bop OsQ)
    (hD3 : D3HypO OsQ) : GuestCompleteModel := by
  intro CM Ht hag seed s w pi hpi hrel hlim hcap hbudget
  have hm : End.MainCompleteCT CM.sem CM.H Ht B2C.fs B2C.cert B2C.cnt B2C.b2cBudget'
      (fun D R b _ t => B1.VerifySub.VsRootTreeEO CM.sem OsQ End.bytecode D R B2C.fs B2C.cert b t)
      (vrOf CM Ht) (CclQP CM.H) (SdQP CM.H) B1.Main.Loop100Q := by
    refine End.mainCompleteC_ofT hag B2C.fs B2C.cert B2C.cnt B2C.b2cBudget'
      (calleesAtC_of_open (b1CompHyps_all CM).callees_open) (B1.Main.fsRowsC_model CM) (B1.Main.bsRowsC_model CM)
      (fun op => B2C.ωArm B1.Sig.xmssArmC op) (fun op => Count.kcWtS CM.sem op) B2C.jtSets
      (B2C.two_le_fs _) _ (fun D R hD lpA sqA outA c hc => vs_completeTO CM (hOpen CM) D R hD lpA sqA outA _ c hc)
      (vrOf CM Ht) (fun off cs args rets b rd t => B1.Digest.CclLoadsQ off cs args rets b rd t ∧
        B1.Digest.CclPreAtC CM.H off cs rd args rets) (ccl_completeT CM)
      (fun sig cells args rets b rd t => B1.Digest.SdLoadsQ sig cells args rets b rd t ∧
        B1.Digest.SdPreAtC CM.H sig cells rd args rets) (sd_completeT CM) (cover_completeT CM)
      ?_ ?_ ?_ ?_
    · intro seed s w pi hpi hN hlim hcaps
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · obtain ⟨-, pic, hpic, hver⟩ := hN.2.1 c hc
        obtain ⟨-, rfl⟩ := B1.Main.stmtAns_of hag hpic
        exact (B1.VerifySub.vs_invC_capAgreesC CM Ht hag seed _ c.fresh c.proof
          (fun layout r h => hlim.stackLog c hc layout r h) (hlim.stream c hc) hver (hcaps c hc)).1
      · obtain ⟨h1, h2, h3, h4, -⟩ := vrOf_spec hag hN hlim hcaps c hc
        exact ⟨h1, h2, h3, h4⟩
    · intro seed s w _ hlim
      rw [mainBound_honestC]
      exact B1.Main.ea_words B2C.fs B2C.calleesHyps_b2c (fun q => loop86_bound_le q) (seed := seed) hlim
    · exact B2C.cntB_le_weight_arm B1.Sig.xmssArmC B1.Sig.xmssArmCS_spec
    · intro seed s w _ hlim op
      rw [mainWeightS_honestC]
      have := B1.Main.ea_weight (B2C.ωArm B1.Sig.xmssArmC op) (Count.kcWt op)
        (B1.Main.ea_wordsOk B2C.fs B2C.calleesHyps_b2c (fun q => loop86_bound_le q)) (seed := seed) hlim
      simp only [B2C.b2cBudget', B2C.b2cBudget, B1.Main.eaBudget, B1.Main.eaInstrs, End.Linear.eval] at this ⊢
      omega
  obtain ⟨rd0, T0, ν, hn, hv, hQ, hH, hw, hc, hmem, himg⟩ := End.honest_of_mainCT' hm
    (B2C.b2c_kfactsAll fun hdr T _ ↦ B2C.kfacts_run hdr T) B2C.cntRetemp seed s w pi hpi hrel hlim hcap
    hbudget
  have hn' : (T0.retemp coreProgram B2C.fs ν 0).name = "main" := by rw [name_retemp]; exact hn
  have hfun : B2C.SemFunctional CM.sem := fun h h' => CM.functional h h'
  obtain ⟨n, hvalid, hsz⟩ := End.validB_of_honestC hfun hn' hH hw hc
  obtain ⟨bufs, ks, hT0, -⟩ := id hQ
  have hW : B1.Main.MainWordsOkC CM.sem B2C.fs CM.H 16 (VsGoodC CM (B1.VerifySub.CapAgreesC CM)) 0
      (honestWordsC Ht seed s w) := by
    refine B1.Main.honestC_wordsOk B2C.fs Ht hag (B1.Main.fsRowsC_model CM) End.bytecode_length hrel
      hpi hlim ?_ ?_
    · intro c hc
      obtain ⟨-, pic, hpic, hver⟩ := hrel.2.1 c hc
      obtain ⟨-, rfl⟩ := B1.Main.stmtAns_of hag hpic
      exact (B1.VerifySub.vs_invC_capAgreesC CM Ht hag seed _ c.fresh c.proof
        (fun layout r h => hlim.stackLog c hc layout r h) (hlim.stream c hc) hver (hcap c hc)).1
    · intro c hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      obtain ⟨h1, h2, h3, h4, -⟩ := vrOf_spec hag hrel hlim hcap i hi
      exact ⟨_, _, h1, h2, h3, h4⟩
  have htot : T0.total B2C.fs < 2 ^ 32 := by
    have := End.words_le_of_size hbudget
    rw [total_retemp] at hw
    omega
  have hbase6 : B1.Main.mainBase B2C.fs 0 (honestWordsC Ht seed s w) 6 ≤ 2 ^ 32 := by
    have hbufs := main_bufs_eq hW hT0 rfl hH.bufsOk
    have hl : 6 < (honestWordsC Ht seed s w).sizes.length := by simp [B1.Main.MainWords.sizes]
    have hT0t : T0.total B2C.fs = B2C.fs "main" + Memory.Tree.totalKids B2C.fs ks + bufs.sum := by
      rw [hT0, total_node]
    have e := List.sum_take_add_sum_drop (honestWordsC Ht seed s w).sizes 6
    have hw' := hw
    rw [total_retemp] at hw'
    have := End.words_le_of_size hbudget
    unfold B1.Main.mainBase
    rw [List.getD_eq_getElem?_getD, getElem?_bases hl, Option.getD_some]
    rw [hbufs] at hT0t
    omega
  obtain ⟨fr, hp⟩ := hD3 CM Ht seed s w (vrOf CM Ht seed s w) (End.hdrOf pi) rd0 T0 ν n
    (fun c => vrOf_spec hag hrel hlim hcap c) hn' hv hQ hH hvalid.2 hmem hbase6
    (by have h1 := hW.nc; have h2 : (honestWordsC Ht seed s w).nc = w.children.length := rfl; omega) himg
  refine ⟨_, fr, hvalid, hsz.trans hbudget, ?_⟩
  apply decodeHonest_of
  · exact decode_count (B2C.b2HypsB hfun) hT0 hH (mainVal_6 B2C.fs rd0 0 _) (by
      have h1 := hW.nc
      have h2 : (honestWordsC Ht seed s w).nc = w.children.length := rfl
      omega)
  · exact decode_stmts (B2C.b2HypsB hfun) hrel hlim hW hv hQ hH htot hmem himg
  · exact hp


/-! ## Naming the frames -/

/-- A valid instance's argument words are its call's. -/
theorem validB_instArgs {S : BlakeSem} {rd : Reader} {args rets : List E} {I : Inst}
    (h : I.t.ValidB S coreProgram rd args rets) : instArgs I = args := by
  cases ht : I.t with
  | node f σ bufs kids =>
    rw [ht] at h
    obtain ⟨fn, hf, hpar, -⟩ := h
    obtain ⟨j, hj⟩ : ∃ j, B2C.idxOf f = some j := by
      unfold B2C.idxOf
      rcases hi : coreProgram.indexOf? f with _ | i
      · rw [B2C.find?_none hi] at hf; cases hf
      · exact ⟨i + 1, rfl⟩
    obtain ⟨i, hji, hi, hnm, hfi, hco, -⟩ := B2C.fn_of_idx hj
    obtain rfl : fn = coreOf j := by rw [hco]; exact Option.some.inj (hf.symm.trans hfi)
    unfold instArgs
    rw [ht]
    simp only [Memory.Tree.name, Memory.Tree.val, hj]
    exact hpar
  | phantom f σ => rw [ht] at h; exact h.elim

theorem names_disjoint : "verify_sub" ∉ B1.VerifySub.openNames ∧ "verify_sub" ∉ B1.osDecNames ∧
    ∀ f ∈ B1.VerifySub.openNames, f ∉ B1.osDecNames := by
  decide +kernel

theorem osInjNames_eq : B1.osInjNames = B1.osDecNames := rfl


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **D3: the children's proofs, decoded off the honest memory.** -/
theorem d3HypO : D3HypO B1.OsQ := by
  intro CM Ht seed s w vr hdr rd0 T0 ν n hvr hn' hv hQ hH hrun hmem hbase6 hnc16 himg
  have hfun : B2C.SemFunctional CM.sem := fun h h' => CM.functional h h'
  have hcan := @CM.canonical
  obtain ⟨bufs, ks, hT0, -⟩ := id hQ
  obtain ⟨b0, k0, hL5, hch⟩ := vs_child_inst hfun hcan hn' hH hrun hT0 rfl
    (fun D R b rd t h => let ⟨σ, bufs, ks, h1, _⟩ := h; ⟨σ, bufs, ks, h1⟩) hQ
  choose kvf Wf σf bf ksf kf htl hk5 hb5 hWm hWt hq hWn hWa hWb hWag using hch
  have hop := fun c (hc : c < w.children.length) => open_child hH (hWm c hc) (hWt c hc) (hq c hc)
  choose σv bufsv ksv ko Jf af hkv hko hfrm hOs hJm hJt hJn hJv ha5 ha1 ha2 hJ1 hJ2 using hop
  have hTt : (T0.retemp coreProgram B2C.fs ν 0).total B2C.fs ≤ 2 ^ 32 := hH.toHonestB.size
  -- the children's regions
  have hWreg : ∀ c (hc : c < w.children.length),
      (Wf c hc).fp + (Wf c hc).t.total B2C.fs ≤ (T0.retemp coreProgram B2C.fs ν 0).total B2C.fs := by
    intro c hc
    have := (insts_total (T0.retemp coreProgram B2C.fs ν 0) 0 hdr (Wf c hc) (hWm c hc)).2
    omega
  have htotW : ∀ c (hc : c < w.children.length), (Wf c hc).t.total B2C.fs = (kvf c hc).total B2C.fs :=
    fun c hc => by rw [hWt c hc, total_retemp]
  have hsep : ∀ c (hc : c < w.children.length) c' (hc' : c' < w.children.length), c ≠ c' → ∀ x,
      (Wf c hc).fp ≤ x → x < (Wf c hc).fp + (Wf c hc).t.total B2C.fs →
      (Wf c' hc').fp ≤ x → x < (Wf c' hc').fp + (Wf c' hc').t.total B2C.fs → False := by
    intro c hc c' hc' hne x h1 h2 h3 h4
    rw [htotW] at h2 h4
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := loop5Q_vs_disjoint hL5 hlt hc' (htl c hc) (htl c' hc') (hk5 c hc) (hb5 c hc)
        (hk5 c' hc') (hb5 c' hc')
      omega
    · have := loop5Q_vs_disjoint hL5 hlt hc (htl c' hc') (htl c hc) (hk5 c' hc') (hb5 c' hc')
        (hk5 c hc) (hb5 c hc)
      omega
  -- the opening roots
  have hJname : ∀ c (hc : c < w.children.length), (Jf c hc).t.name =
      B1.VerifySub.openName (B1.VerifySub.layoutOf End.bytecode (vr c).1.logMem (vr c).1.rows).stackLog
        (vr c).1.rate := fun c hc => by
    rw [hJn c hc, (hfrm c hc).layout, (hfrm c hc).rate]
  have hok : ∀ c (hc : c < w.children.length), (vr c).1.OkC CM End.bytecode (vr c).2 :=
    fun c hc => ((hvr c hc).1).2.1
  have hJopen : ∀ c (hc : c < w.children.length), (Jf c hc).t.name ∈ B1.VerifySub.openNames :=
    fun c hc => by
      rw [hJname c hc]
      exact B1.openName_mem (hok c hc).stack_ge (hok c hc).stack_le (hok c hc).rate_ge (hok c hc).rate_le
  have hJargs : ∀ c (hc : c < w.children.length), instArgs (Jf c hc) = B1.VerifySub.vsOpenArgs (σv c hc) :=
    fun c hc => validB_instArgs (hJv c hc)
  have hinj : ∀ c (hc : c < w.children.length), B1.OsInj (Jf c hc).fp (Jf c hc).t := fun c hc =>
    B1.os_inj (hok c hc).stack_ge (hok c hc).stack_le (hok c hc).rate_ge (hok c hc).rate_le
      (hJname c hc) (hJv c hc)
      (insts_placedAt (T0.retemp coreProgram B2C.fs ν 0) 0 hdr hH.placed (Jf c hc) (hJm c hc))
  have hJb : ∀ c (hc : c < w.children.length), (Jf c hc).fp + (Jf c hc).t.total B2C.fs ≤ 2 ^ 32 :=
    fun c hc => by have := hWreg c hc; have := hJ2 c hc; omega
  -- the designated instances
  let Is : Inst → Prop := fun I => (∃ c hc, I = Wf c hc) ∨ (∃ c hc, I = Jf c hc) ∨
    (∃ c hc, I ∈ (Jf c hc).t.insts B2C.fs coreProgram.loop B2C.H (Jf c hc).fp (Jf c hc).hdr ∧
      I.t.name ∈ B1.osDecNames)
  obtain ⟨nd1, nd2, nd3⟩ := names_disjoint
  have h133 := mainFrame_133 (B2C.b2HypsB hfun) hT0 hH (W := honestWordsC Ht seed s w) rfl
  have hU : ∀ I I', Is I → Is I' → I'.t.name = I.t.name → instArgs I' = instArgs I → I'.fp = I.fp := by
    rintro I I' (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, hIm, hIn⟩)
      (⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩ | ⟨c', hc', hI'm, hI'n⟩) hname hargs
    · rw [hWa, hWa] at hargs
      obtain rfl := vsArgsAt_inj h133 (by omega) (by omega) (by omega) hargs
      rfl
    · have h := hJopen c' hc'; rw [hname, hWn] at h; exact absurd h nd1
    · have h := hI'n; rw [hname, hWn] at h; exact absurd h nd2
    · have h := hJopen c hc; rw [← hname, hWn] at h; exact absurd h nd1
    · rw [hJargs, hJargs] at hargs
      have e5 := congrArg (fun l => l[5]?) hargs
      simp only [ha5] at e5
      have ha := Parameters.gpow_injOn
        (show af c' hc' ∈ Set.Iio (2 ^ 64 - 1) by have := hWreg c' hc'; have := ha2 c' hc'; simp; omega)
        (show af c hc ∈ Set.Iio (2 ^ 64 - 1) by have := hWreg c hc; have := ha2 c hc; simp; omega)
        (Parameters.ofK_injective (Option.some.inj e5))
      by_cases hcc : c = c'
      · subst hcc; rfl
      · exact (hsep c hc c' hc' hcc (af c hc) (ha1 c hc) (ha2 c hc) (ha ▸ ha1 c' hc')
          (ha ▸ ha2 c' hc')).elim
    · have h := hI'n; rw [hname] at h; exact absurd h (nd3 _ (hJopen c hc))
    · have h := hIn; rw [← hname, hWn] at h; exact absurd h nd2
    · have h := hIn; rw [← hname] at h; exact absurd h (nd3 _ (hJopen c' hc'))
    · obtain ⟨j, hj, -⟩ := B1.osDec_plain _ (List.mem_append_left _ hIn)
      obtain ⟨⟨a, haI, ha1', ha2'⟩, huniq⟩ := hinj c hc (hJb c hc) B2C.H (Jf c hc).hdr I hIm j hj
        (by rw [osInjNames_eq]; exact hIn)
      obtain ⟨⟨a', haI', ha1'', ha2''⟩, -⟩ := hinj c' hc' (hJb c' hc') B2C.H (Jf c' hc').hdr I' hI'm j
        (by rw [hname]; exact hj) (by rw [osInjNames_eq]; exact hI'n)
      have hmaps : (coreOf j).params.map I'.t.val = (coreOf j).params.map I.t.val := by
        unfold instArgs at hargs
        rw [hname, hj] at hargs
        exact hargs
      rw [hmaps, hname, haI] at haI'
      have ha := Parameters.gpow_injOn
        (show a ∈ Set.Iio (2 ^ 64 - 1) by have := hJb c hc; simp; omega)
        (show a' ∈ Set.Iio (2 ^ 64 - 1) by have := hJb c' hc'; simp; omega)
        (Parameters.ofK_injective (Option.some.inj haI'))
      subst ha
      by_cases hcc : c = c'
      · subst hcc
        exact huniq I' hI'm hname hmaps
      · exact (hsep c hc c' hc' hcc a (by have := hJ1 c hc; omega) (by have := hJ2 c hc; omega)
          (by have := hJ1 c' hc'; omega) (by have := hJ2 c' hc'; omega)).elim
  -- each child's proof
  refine ⟨frOf Is, fun c hc => ?_⟩
  have hfrW : frOf Is "verify_sub" (vsArgsAt (honest coreProgram B2C.fs B2C.H B2C.C hdr
      (T0.retemp coreProgram B2C.fs ν 0)) c) = some (Wf c hc).fp := by
    rw [← hWn c hc, ← hWa c hc]
    exact frOf_eq (Or.inl ⟨c, hc, rfl⟩) fun I' hI' => hU _ I' (Or.inl ⟨c, hc, rfl⟩) hI'
  -- the opening's root: a node, its body at its frame
  obtain ⟨σJ, bJ, kJ, hJt'⟩ : ∃ σJ bJ kJ, (Jf c hc).t = .node (B1.VerifySub.openName
      (B1.VerifySub.vsLayout End.bytecode (σv c hc)).stackLog (B1.VerifySub.vsRate (σv c hc))) σJ bJ kJ := by
    have hvJ := hJv c hc
    have hnJ := hJn c hc
    rcases h : (Jf c hc).t with ⟨g, σJ, bJ, kJ⟩ | ⟨g, σJ⟩
    · rw [h] at hnJ
      exact ⟨σJ, bJ, kJ, by rw [← hnJ]; rfl⟩
    · rw [h] at hvJ; exact hvJ.elim
  obtain ⟨jJ, hjJ, hjJ1, hpJ, hmJ, hsJ⟩ := B1.osDec_plain _ (List.mem_append_right _
    (show B1.VerifySub.openName (B1.VerifySub.vsLayout End.bytecode (σv c hc)).stackLog
      (B1.VerifySub.vsRate (σv c hc)) ∈ B1.VerifySub.openNames by rw [← hJn c hc]; exact hJopen c hc))
  have hbJ := honest_bodyAt_plain (n := n) hfun hcan hn' hH hrun (hJm c hc) hJt' hjJ hjJ1 ⟨hpJ, hmJ, hsJ⟩
    (hJv c hc)
  have hfrJ : frOf Is (B1.VerifySub.openName (B1.VerifySub.vsLayout End.bytecode (σv c hc)).stackLog
      (B1.VerifySub.vsRate (σv c hc))) (B1.VerifySub.vsOpenArgs (σv c hc)) = some (Jf c hc).fp := by
    rw [← hJargs c hc, ← hJn c hc]
    exact frOf_eq (Or.inr (Or.inl ⟨c, hc, rfl⟩)) fun I' hI' => hU _ I' (Or.inr (Or.inl ⟨c, hc, rfl⟩)) hI'
  -- the openings decode
  have hO : ∀ σ' bufs' ks', kvf c hc = .node "verify_sub" σ' bufs' ks' →
      Located.wOLB (honestSem hdr (T0.retemp coreProgram B2C.fs ν 0) n) (frOf Is)
        (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0))
        (B1.VerifySub.openName (B1.VerifySub.vsLayout End.bytecode σ').stackLog (B1.VerifySub.vsRate σ'))
        (B1.VerifySub.vsOpenArgs σ') (B1.VerifySub.vsOpenRets σ') = (vr c).1.os := by
    intro σ' bufs' ks' h'
    rw [hkv c hc] at h'
    simp only [Memory.Tree.node.injEq] at h'
    obtain ⟨-, rfl, -, -⟩ := h'
    rw [B1.wOLB_eq]
    unfold B1.frameValsOf
    rw [Located.frameOfB_of_bodyAt hfrJ hbJ]
    obtain ⟨b, hos⟩ := hOs c hc
    rw [(hfrm c hc).layout, (hfrm c hc).rate]
    refine hos _ (B1.frameValsOf (honestSem hdr (T0.retemp coreProgram B2C.fs ν 0) n) (frOf Is)
      (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0))) _ ?_ ?_ ?_
    · intro q hq
      have hq' : q ∈ (Jf c hc).t.loadEqns coreProgram := by
        rw [hJt c hc, loadEqns_retemp coreProgram_fresh]; exact hq
      exact honest_read_inst hH.toHonestB (hJm c hc) q hq'
    · obtain ⟨J0, rest, hJ0, hJ0t, hJ0fp, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop)
        (H := B2C.H) (Jf c hc).t (Jf c hc).fp (Jf c hc).hdr
      refine B1.kidsLink_of_vagree (ν := ν) (vagree_honest hfun hcan hn' hH hrun (hJm c hc)
        fun K hK hKn => frOf_eq (Or.inr (Or.inr ⟨c, hc, hK, hKn⟩))
          fun I' hI' => hU _ I' (Or.inr (Or.inr ⟨c, hc, hK, hKn⟩)) hI') (ko c hc) J0
        (by rw [hJ0]; exact List.mem_cons_self) (by rw [hJ0t, hJ0fp]; exact hJt c hc)
    · refine B1.nodeAgree_of_retemp (ν := ν) (fp := (Jf c hc).fp) ?_
      rw [← hJt c hc]
      have hJt2 := hJt'
      rw [(hfrm c hc).layout, (hfrm c hc).rate] at hJt2
      exact honest_nodeAgree hfun hn' hH (hJm c hc) hJt2
  -- the proof
  have hvW : ∃ args' rets', (Wf c hc).t.ValidB CM.sem coreProgram
      (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read args' rets' := by
    have hWt' := hWt c hc
    rw [hkv c hc, retemp_node] at hWt'
    exact honest_inst_valid hH (hWm c hc) hWt'
  have hld : ∀ q ∈ (kvf c hc).loadEqns coreProgram,
      (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read q.1 = some q.2 := by
    intro q hq
    have hq' : q ∈ (Wf c hc).t.loadEqns coreProgram := by
      rw [hWt c hc, loadEqns_retemp coreProgram_fresh]; exact hq
    exact honest_read_inst hH.toHonestB (hWm c hc) q hq'
  rw [vs_proof_of_inst (hWt c hc) (hq c hc).toE hvW hfrW (hWb c hc) (hWag c hc) hld hO]
  exact ((hvr c) hc).2.2.2.2


/-! ## L2 and T6-det -/

/-- **L2: the guest's completeness over every completeness model.** -/
theorem guestCompleteModel : GuestCompleteModel :=
  guestCompleteModel_ofO B1.open_stacked_completeAtBCL_b2c d3HypO

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-- **T6-det**: `idealVerify_complete''` with L2 discharged (`guestCompleteModel`). -/
theorem idealVerify_complete_det (T : HonestTree) {fuel : ℕ}
    (hρ : validRate ρ) (hv : T.Valid H) (hlim : T.WithinLimits' H ρ pfuel)
    (hpow : T.PowFound H ρ pfuel) (hw : T.WeightsNonzero H ρ pfuel)
    (hroots : T.RootsInjAt H ρ pfuel) (hfuel : T.size ≤ fuel) :
    ∃ s ip, honestIdeal H ρ pfuel T = some (s, ip) ∧ s.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest ip fuel s = true :=
  idealVerify_complete'' H ρ pfuel guestCompleteModel T hρ hv hlim hpow hw hroots hfuel

end
end LeanVM.E2E.Complete
