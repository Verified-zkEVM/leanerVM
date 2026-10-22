/-
  LeanVM.E2E.Complete.DecodeAssembly

  L2's `GuestCompleteModel` from the decoding of the children's proofs: the execution, the count
  and the statements, over every completeness model.
-/

module

public import LeanVM.E2E.Complete.DecodeHV
public import LeanVM.E2E.Complete.DecodeCount
public import LeanVM.E2E.Complete.HonestVs

/-!
# Assembling `GuestCompleteModel`

`mainCompleteC_ofT` at `calleesAtC_of_open`'s callees in tree form (`DecodeHV.lean`), `verify_sub`'s
trees decoding the children's runs at an opening predicate `OsQ` the Whir side places
(`hOpen`), the runs chosen per child (`vrOf`: a good run with the child's statement digest, seed,
fresh claims and proof, `vs_invC_capAgreesC`). The honest tree (`honest_of_mainCT'`) runs validly
(`validB_of_honestC`), and V_I's decoder reads off its memory the children's count
(`decode_count`) and statements (`decode_stmts`); the proofs are `D3Hyp OsQ`'s.

* `vrOf`, `vrOf_spec`: the children's runs;
* `D3Hyp OsQ`: frames at which the decoder reads the children's proofs off the honest memory;
* `guestCompleteModel_of`: `GuestCompleteModel` from `hOpen` and `D3Hyp OsQ`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Node
open LeanVM.Guest.B1.Main (calleeBd VsGoodC honestWordsC mainIn mainVal mainRunAt mainIQ MainQ
  calleesAtC_of_open)

@[expose] public section

theorem nonempty_vsRun : Nonempty (B1.VerifySub.VsData × B1.VerifySub.VsRunC) :=
  ⟨(by constructor <;> first | exact default | (constructor <;> exact default),
    by constructor <;> exact default)⟩

/-- **A child's run**: a good run over the model with the child's statement digest, seed, fresh
claims and proof. -/
def VrP (CM : CompModel) (Ht : Compile.Bytes → Digest) (seed : Digest) (w : NodeWitness) (c : ℕ)
    (p : B1.VerifySub.VsData × B1.VerifySub.VsRunC) : Prop :=
  ∀ hc : c < w.children.length, VsGoodC CM (B1.VerifySub.CapAgreesC CM) p.1 p.2 ∧
    p.1.pi = B1.Main.statementDigestH Ht seed w.children[c].statement ∧ p.1.seed = seed ∧
    p.2.fresh p.1 = w.children[c].fresh ∧ p.1.proof = w.children[c].proof

/-- **The children's runs**, chosen. -/
noncomputable def vrOf (CM : CompModel) (Ht : Compile.Bytes → Digest) (seed : Digest)
    (_s : NodeStatement) (w : NodeWitness) (c : ℕ) : B1.VerifySub.VsData × B1.VerifySub.VsRunC :=
  @Classical.epsilon _ nonempty_vsRun (VrP CM Ht seed w c)

theorem vrOf_spec {CM : CompModel} {Ht : Compile.Bytes → Digest}
    (hag : ∀ x d, CM.H x = some d → d = Ht x) {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hN : NodeRelWith CM.H B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow End.bytecode seed s w)
    (hlim : End.Limits s w) (hcaps : CapsAgreeWith Ht seed w) (c : ℕ) :
    VrP CM Ht seed w c (vrOf CM Ht seed s w c) := by
  refine @Classical.epsilon_spec _ (VrP CM Ht seed w c) ?_
  by_cases hc : c < w.children.length
  · have hm := List.getElem_mem hc
    obtain ⟨-, pic, hpic, hver⟩ := hN.2.1 _ hm
    obtain ⟨-, rfl⟩ := B1.Main.stmtAns_of hag hpic
    obtain ⟨-, D, R, h2, h3, h4, h5, h6⟩ := B1.VerifySub.vs_invC_capAgreesC CM Ht hag seed _
      w.children[c].fresh w.children[c].proof (fun layout r h => hlim.stackLog _ hm layout r h)
      (hlim.stream _ hm) hver (hcaps _ hm)
    exact ⟨(D, R), fun _ => ⟨h2, h3, h4, h5, h6⟩⟩
  · exact ⟨nonempty_vsRun.some, fun h => absurd h hc⟩

/-- **What decoding the children's proofs takes** (D3): on the honest memory of `main`'s
re-chosen tree, from `main`'s tree form with `verify_sub`'s trees decoding the children's runs at
`OsQ`, frames at which V_I's decoder reads each child's proof. -/
def D3Hyp (OsQ : ℕ → ℕ → List Opening → ℕ → Memory.Tree → Prop) : Prop :=
  ∀ (CM : CompModel) (Ht : Compile.Bytes → Digest) (seed : Digest) (s : NodeStatement)
    (w : NodeWitness) (vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC) (hdr : E × E)
    (rd0 : Reader) (T0 : Memory.Tree) (ν : ℕ → String → Val → V → E) (n : ℕ),
    (∀ c, VrP CM Ht seed w c (vr c)) →
    (T0.retemp coreProgram B2C.fs ν 0).name = "main" →
    T0.ValidB CM.sem coreProgram rd0 [] [] →
    MainQ (fun D R b _ t => B1.VerifySub.VsRootTreeE CM.sem OsQ End.bytecode D R B2C.fs B2C.cert b t) vr
      (CclQP CM.H) (SdQP CM.H) B1.Main.Loop100Q (mainIQ B2C.fs 0 (honestWordsC Ht seed s w)) B2C.fs
      w.children.length 0 (mainVal rd0 (mainRunAt B2C.fs 0 (honestWordsC Ht seed s w))) rd0 T0 →
    HonestAtB CM.sem coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0) B2C.cert
      (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read [] [] →
    runB CM.sem guest (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) n
      Regs.initial = some (Regs.final guest) →
    B1.Main.MemL rd0 (mainIn B2C.fs 0 (honestWordsC Ht seed s w)) →
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
theorem guestCompleteModel_of {OsQ : ℕ → ℕ → List Opening → ℕ → Memory.Tree → Prop}
    (hOpen : ∀ CM : CompModel, B1.VerifySub.CompleteOpenAtBCL CM B2C.fs B2C.cert 16
      (B1.VerifySub.CapAgreesC CM) B2C.calleesHyps_b2c.Bop OsQ)
    (hD3 : D3Hyp OsQ) : GuestCompleteModel := by
  intro CM Ht hag seed s w pi hpi hrel hlim hcap hbudget
  have hm : End.MainCompleteCT CM.sem CM.H Ht B2C.fs B2C.cert B2C.cnt B2C.b2cBudget'
      (fun D R b _ t => B1.VerifySub.VsRootTreeE CM.sem OsQ End.bytecode D R B2C.fs B2C.cert b t)
      (vrOf CM Ht) (CclQP CM.H) (SdQP CM.H) B1.Main.Loop100Q := by
    refine End.mainCompleteC_ofT hag B2C.fs B2C.cert B2C.cnt B2C.b2cBudget'
      (calleesAtC_of_open (b1CompHyps_all CM).callees_open) (B1.Main.fsRowsC_model CM) (B1.Main.bsRowsC_model CM)
      (fun op => B2C.ωArm B1.Sig.xmssArmC op) (fun op => Count.kcWtS CM.sem op) B2C.jtSets
      (B2C.two_le_fs _) _ (fun D R hD lpA sqA outA c hc => vs_completeT CM (hOpen CM) D R hD lpA sqA outA _ c hc)
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
  obtain ⟨fr, hp⟩ := hD3 CM Ht seed s w (vrOf CM Ht seed s w) (End.hdrOf pi) rd0 T0 ν n
    (fun c => vrOf_spec hag hrel hlim hcap c) hn' hv hQ hH hvalid.2 hmem himg
  refine ⟨_, fr, hvalid, hsz.trans hbudget, ?_⟩
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
  apply decodeHonest_of
  · exact decode_count (B2C.b2HypsB hfun) hT0 hH (mainVal_6 B2C.fs rd0 0 _) (by
      have h1 := hW.nc
      have h2 : (honestWordsC Ht seed s w).nc = w.children.length := rfl
      omega)
  · exact decode_stmts (B2C.b2HypsB hfun) hrel hlim hW hv hQ hH htot hmem himg
  · exact hp

end
end LeanVM.E2E.Complete
