/-
  LeanVM.E2E.Complete.GuestModelBig

  L2 with the memory padded as leanVM's prover pads it: a node's execution of committed size above
  `2^21`, so of at least 22 stacked variables, the guest's floor on a child's stack.
-/

module

public import LeanVM.E2E.Complete.DecodePad

/-!
# `GuestCompleteModel`, padded

`guestCompleteModel`'s execution runs on the honest memory, of `2^logMem` words for the words its
tree allocates; a small node's committed size may be below `2^21`, so its stack below the 22
variables a parent admits of a child (`End.Limits.stackLog`). leanVM's prover pads the memory
with zero cells until the stack reaches 22 variables (`leanvm_core/src/cpu/execute.rs:909-918`).

`guestCompleteModel_big`: the same hypotheses give an execution of committed size in
`(2^21, 2^28]` whose children decode. Above `2^21` it is `guestCompleteModel`'s; else the memory
has at most `2^19` words and its zero padding to `2^19` words (`padImage`) runs the same steps
(`runB_of_ext`), of committed size in `(2^21, 2^22]`, and V_I's decoder reads the same count and
statements off it (they read with the default `0`) and the same proofs (`d3HypO_ext`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Node LeanVM.Protocol.LeanIsa
open LeanVM.Guest.B1.Main (calleeBd vsExtLR VsGoodC honestWordsC mainIn mainVal mainRunAt mainIQ MainQ
  calleesAtC_of_open)

@[expose] public section

/-- **L2, padded**: `GuestCompleteModel` with the execution's committed size above `2^21`. -/
def GuestCompleteModelBig : Prop :=
  ∀ (CM : CompModel) (Ht : Bytes → Digest), (∀ x d, CM.H x = some d → d = Ht x) →
    ∀ (seed : Digest) (s : NodeStatement) (w : NodeWitness) (pi : Digest),
      statementDigestWith CM.H seed s = some pi →
      NodeRelWith CM.H B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow End.bytecode seed s w →
      End.Limits s w → CapsAgreeWith Ht seed w →
      B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28 →
      ∃ (t : Trace Guest.guest) (fr : Frames),
        ValidExecutionB CM.sem Guest.guest (End.publicInputOf pi) t ∧
          t.committedSizeB CM.sem ≤ 2 ^ 28 ∧ 2 ^ 21 < t.committedSizeB CM.sem ∧ DecodeHonest fr t w

/-! ## The padded trace -/

/-- `cellAt` reads with the default `0`. -/
theorem cellAt_ext {rd rd' : Reader} (h : ∀ a, (rd' a).getD 0 = (rd a).getD 0) :
    B1.Main.cellAt rd' = B1.Main.cellAt rd := by
  funext p k
  simp only [B1.Main.cellAt, h]

/-- **A child's statement as the decoder reads it** reads with the default `0`. -/
theorem kidStmt_ext {rd rd' : Reader} (h : ∀ a, (rd' a).getD 0 = (rd a).getD 0)
    (F : B1.Main.Frame) (T : ℕ) (cnt : ℕ → ℕ) (c : ℕ) :
    B1.Main.kidStmt rd' F T cnt c = B1.Main.kidStmt rd F T cnt c := by
  have hx : B1.Main.entryX rd' = B1.Main.entryX rd := by
    funext T s
    simp only [B1.Main.entryX, cellAt_ext h]
  simp only [B1.Main.kidStmt, B1.Main.kidSlots, B1.Main.slotOf, hx, B1.Main.entryS,
    B1.Main.daOf, B1.Main.decDefer, B1.Main.readCells, cellAt_ext h]

theorem countOf_ext {rd rd' : Reader} (h : ∀ a, (rd' a).getD 0 = (rd a).getD 0) (σ : Val) :
    B1.Main.countOf rd' σ = B1.Main.countOf rd σ := by
  funext c
  simp only [B1.Main.countOf, cellAt_ext h]

variable {Sm : BlakeSem}

/-- **The padded execution**: an execution of committed size at most `2^21` runs, padded to `2^19`
words, with committed size in `(2^21, 2^28]`. -/
theorem padded_spec {prog : Semantics.Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecutionB Sm prog input t) (hsmall : t.committedSizeB Sm ≤ 2 ^ 21) :
    t.κ ≤ 19 ∧ ValidExecutionB Sm prog input ⟨19, padImage 19 t.image, t.steps⟩ ∧
      (⟨19, padImage 19 t.image, t.steps⟩ : Trace prog).committedSizeB Sm ≤ 2 ^ 28 ∧
      2 ^ 21 < (⟨19, padImage 19 t.image, t.steps⟩ : Trace prog).committedSizeB Sm := by
  obtain ⟨⟨h16, h32, h0, h1⟩, hrun⟩ := hv
  rw [committedSizeB_split] at hsmall
  have hlog : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
  have hκ : t.κ ≤ 19 := by
    by_contra hc
    push Not at hc
    have : (2 : ℕ) ^ 20 ≤ 2 ^ t.κ := Nat.pow_le_pow_right (by norm_num) hc
    omega
  have h64 : (19 : ℕ) < 64 := by norm_num
  have hrd : ∀ a v, t.image.read a = some v → (padImage 19 t.image).read a = some v :=
    fun _ _ h ↦ padImage_read_of h64 hκ h
  have hcount : ∀ op, (⟨19, padImage 19 t.image, t.steps⟩ : Trace prog).countB Sm op =
      t.countB Sm op := fun op ↦ runCountB_of_ext hrd op t.steps hrun
  have hparts : countsPart Sm (⟨19, padImage 19 t.image, t.steps⟩ : Trace prog) =
      countsPart Sm t := by
    unfold countsPart
    simp only [hcount]
  have hsz := committedSizeB_split (Sm := Sm) (⟨19, padImage 19 t.image, t.steps⟩ : Trace prog)
  rw [hparts] at hsz
  have e19 : (2 : ℕ) ^ (19 : ℕ) = 524288 := by norm_num
  dsimp only at hsz
  rw [e19] at hsz
  exact ⟨hκ, ⟨⟨by show 16 ≤ 19; omega, by show 19 ≤ 32; omega, padImage_read_of h64 hκ h0,
    padImage_read_of h64 hκ h1⟩, runB_of_ext hrd _ hrun⟩, by omega, by omega⟩

/-! ## L2, padded -/

/-- **What decoding the children's proofs off the padded memory takes** (`D3HypO`, on every
extension of the honest memory of `2^κ'` words, `16 ≤ κ' ≤ 32`). -/
def D3HypOExt (OsQ : ℕ → ℕ → List Opening → ℕ → Memory.Tree → Prop) : Prop :=
  ∀ (CM : CompModel) (Ht : Compile.Bytes → Digest) (seed : Digest) (s : NodeStatement)
    (w : NodeWitness) (vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC) (hdr : E × E)
    (rd0 : Reader) (T0 : Memory.Tree) (ν : ℕ → String → Val → V → E) (n : ℕ),
    (∀ c, VrP CM Ht seed w c (vr c)) →
    (T0.retemp coreProgram B2C.fs ν 0).name = "main" →
    MainQ (fun D R b _ t => B1.VerifySub.VsRootTreeEO CM.sem OsQ End.bytecode D R B2C.fs B2C.cert b t) vr
      (CclQP CM.H) (SdQP CM.H) B1.Main.Loop100Q (mainIQ B2C.fs 0 (honestWordsC Ht seed s w)) B2C.fs
      w.children.length 0 (mainVal rd0 (mainRunAt B2C.fs 0 (honestWordsC Ht seed s w))) rd0 T0 →
    HonestAtB CM.sem coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0) B2C.cert
      (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read [] [] →
    runB CM.sem guest (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) n
      Regs.initial = some (Regs.final guest) →
    B1.Main.mainBase B2C.fs 0 (honestWordsC Ht seed s w) 6 ≤ 2 ^ 32 → w.children.length ≤ 16 →
    ∀ {κ' : ℕ} {L' : MemImage κ'},
      MemExt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) L' →
      minLogMem ≤ κ' → κ' ≤ maxLogMem →
      ∃ fr : Frames, ∀ c (hc : c < w.children.length),
        Located.wVsLB (honestSem hdr (T0.retemp coreProgram B2C.fs ν 0) n) fr L' (vsArgsAt L' c) [] =
          w.children[c].proof

theorem d3HypOExt : D3HypOExt B1.OsQ :=
  fun CM Ht seed s w vr hdr rd0 T0 ν n hvr hn' hQ hH hrun hbase6 hnc16 _ _ hX h16' h32' ↦
    d3HypO_ext CM Ht seed s w vr hdr rd0 T0 ν n hvr hn' hQ hH hrun hbase6 hnc16 hX h16' h32'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **L2 with the memory padded, from its pieces** (`guestCompleteModel_ofO`): the Whir side's
`open_stacked` in tree form at `OsQ` and the decoding of the children's proofs off the honest
memory and its extensions. -/
theorem guestCompleteModelBig_ofO {OsQ : ℕ → ℕ → List Opening → ℕ → Memory.Tree → Prop}
    (hOpen : ∀ CM : CompModel, B1.VerifySub.CompleteOpenAtBCL CM B2C.fs B2C.cert 16
      (B1.VerifySub.CapAgreesC CM) B2C.calleesHyps_b2c.Bop OsQ)
    (hD3 : D3HypO OsQ) (hD3X : D3HypOExt OsQ) : GuestCompleteModelBig := by
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
  have hW6 : B1.Main.mainBase B2C.fs 0 (honestWordsC Ht seed s w) 6 ≤ 2 ^ 32 := hbase6
  have hnc : w.children.length ≤ 16 := by
    have h1 := hW.nc; have h2 : (honestWordsC Ht seed s w).nc = w.children.length := rfl; omega
  have hcnt := decode_count (B2C.b2HypsB hfun) hT0 hH (mainVal_6 B2C.fs rd0 0 _) (by
      have h1 := hW.nc
      have h2 : (honestWordsC Ht seed s w).nc = w.children.length := rfl
      omega)
  have hst := decode_stmts (B2C.b2HypsB hfun) hrel hlim hW hv hQ hH htot hmem himg
  by_cases hbig : 2 ^ 21 < (⟨_, honest coreProgram B2C.fs B2C.H B2C.C (End.hdrOf pi)
      (T0.retemp coreProgram B2C.fs ν 0), n⟩ : Trace guest).committedSizeB CM.sem
  · obtain ⟨fr, hp⟩ := hD3 CM Ht seed s w (vrOf CM Ht seed s w) (End.hdrOf pi) rd0 T0 ν n
      (fun c => vrOf_spec hag hrel hlim hcap c) hn' hv hQ hH hvalid.2 hmem hW6 hnc himg
    exact ⟨_, fr, hvalid, hsz.trans hbudget, hbig, decodeHonest_of hcnt hst hp⟩
  push Not at hbig
  obtain ⟨hκ, hvalid', hsz', hbig'⟩ := padded_spec hvalid hbig
  have h64 : (19 : ℕ) < 64 := by norm_num
  have hX := memExt_padImage h64 hκ (honest coreProgram B2C.fs B2C.H B2C.C (End.hdrOf pi)
    (T0.retemp coreProgram B2C.fs ν 0))
  obtain ⟨fr, hp⟩ := hD3X CM Ht seed s w (vrOf CM Ht seed s w) (End.hdrOf pi) rd0 T0 ν n
    (fun c => vrOf_spec hag hrel hlim hcap c) hn' hQ hH hvalid.2 hW6 hnc hX (by decide) (by decide)
  refine ⟨_, fr, hvalid', hsz', hbig', ?_⟩
  have hsem : Value.tableSem (Trace.blakeRows blakeFree
      (⟨19, padImage 19 (honest coreProgram B2C.fs B2C.H B2C.C (End.hdrOf pi)
        (T0.retemp coreProgram B2C.fs ν 0)), n⟩ : Trace guest)) =
      honestSem (End.hdrOf pi) (T0.retemp coreProgram B2C.fs ν 0) n :=
    honestSem_ext (fun h ↦ CM.canonical h) hvalid.2 hX
  have hmf : mainFrame (padImage 19 (honest coreProgram B2C.fs B2C.H B2C.C (End.hdrOf pi)
      (T0.retemp coreProgram B2C.fs ν 0))) = mainFrame (honest coreProgram B2C.fs B2C.H B2C.C
      (End.hdrOf pi) (T0.retemp coreProgram B2C.fs ν 0)) := hX.valG _ _
  apply decodeHonest_of
  · show B1.Main.gLog (mainFrame (padImage 19 _) (.n 6)) = _
    rw [hmf]; exact hcnt
  · intro c hc
    show B1.Main.kidStmt (padImage 19 _).read (B1.Main.frameOf (mainFrame (padImage 19 _)))
      (B1.Main.gLog (mainFrame (padImage 19 _) (.n 58)))
      (B1.Main.countOf (padImage 19 _).read (mainFrame (padImage 19 _))) c = _
    rw [hmf, kidStmt_ext hX.getD, countOf_ext hX.getD]
    exact hst c hc
  · intro c hc
    show Located.wVsLB (Value.tableSem (Trace.blakeRows blakeFree
      (⟨19, padImage 19 _, n⟩ : Trace guest))) fr _ _ [] = _
    rw [hsem]
    exact hp c hc

/-- **L2 with the memory padded**: the guest's completeness over every completeness model, by an
execution of committed size above `2^21`. -/
theorem guestCompleteModel_big : GuestCompleteModelBig :=
  guestCompleteModelBig_ofO B1.open_stacked_completeAtBCL_b2c d3HypO d3HypOExt

end
end LeanVM.E2E.Complete
