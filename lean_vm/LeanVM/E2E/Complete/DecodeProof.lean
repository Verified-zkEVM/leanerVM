/-
  LeanVM.E2E.Complete.DecodeProof

  Each child's `verify_sub` call as an honest instance at V_I's frame: its body holds there under
  the honest run's table, its argument words are the decoder's, and the decoder's valuation there
  agrees with it.
-/

module

public import LeanVM.E2E.Complete.DecodeFrames
public import LeanVM.E2E.Complete.DecodeVsArgs
public import LeanVM.E2E.Complete.DecodeVsAgree
public import LeanVM.E2E.Complete.HonestVs
public import LeanVM.E2E.Complete.DecodeRegions

/-!
# The children's `verify_sub` instances

Along `main`'s tree form (`MainQ`, `Loop5Q`), on the honest memory of the re-chosen tree:

* `loop5_vs_valid`: an iteration's `verify_sub` callee is valid on the call's words
  (`65, 66, 13, 14, 16, 6, 79` of the iteration, no returns);
* `vs_child_inst`: child `c`'s `verify_sub` instance `W`, the re-chosen tree of the iteration's
  callee `kv` (satisfying `VsQ` at child `c`'s run), with V_I's argument words (`vsArgsAt`), its
  body holding at its frame under the honest run's table (`honest_vs_bodyAt`, the exponent tables
  handed down from `main`, `honest_exp_root`, `honest_exp_loop`), and the decoder's valuation there
  agreeing with it on its named cells (`honest_valAt`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Guest.B1.VerifySub (openName)

@[expose] public section

/-- **An iteration's `verify_sub` callee is valid on the call's words.** -/
theorem loop5_vs_valid {S : BlakeSem} {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree}
    {args rets : List E} (hv : (Memory.Tree.node "__loop5" σ bufs kids).ValidB S coreProgram rd args rets)
    {kw : Memory.Tree} (hk : kids[5]? = some kw) :
    kw.ValidB S coreProgram rd ([.n 65, .n 66, .n 13, .n 14, .n 16, .n 6, .n 79].map σ) [] := by
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hv
  obtain rfl : fn = Data.core35 := Option.some.inj (hf.symm.trans B1.Main.find_loop5)
  have hw' : walk σ (Fn.body Data.core35) = .ret (B1.Main.loop5Pre.flatMap (slEvs σ)) [] := by
    rw [B1.Main.core35_split]; exact walk_straight σ [] _ B1.Main.loop5_parts.1
  rw [hw'] at hw
  obtain ⟨rfl, -⟩ := Out.ret.inj hw
  obtain ⟨p1, -, -, p4, -⟩ := B1.Main.loop5_parts
  obtain ⟨-, -, -, e4⟩ := straight_parts σ _ p1
  rw [e4, p4] at hkv
  obtain ⟨-, hget⟩ := B2C.kidsValidB_get hkv
  obtain ⟨k, hk', -, hval⟩ := hget 5 ⟨"verify_sub", [.n 65, .n 66, .n 13, .n 14, .n 16, .n 6, .n 79], [],
    true⟩ (by simp [B1.Main.loop5Fronts, mkCall])
  obtain rfl : k = kw := Option.some.inj (hk'.symm.trans hk)
  exact hval rfl



theorem vsProofVars_uses : ∀ v ∈ vsProofVars, v ∈ Stmt.usesList (Fn.body Data.core15) := by
  decide +kernel

/-- **Child `c`'s proof, decoded at its `verify_sub` instance's frame**: when the frames name the
instance, its body holds there, the decoder's valuation agrees with it, and the openings decode to
the run's: V_I's decoder (`wVsLB`) gives the run's proof. -/
theorem vs_proof_of_inst {S Sd : BlakeSem} {OsQ : ℕ → ℕ → List Opening → ℕ → Memory.Tree → Prop}
    {D : B1.VerifySub.VsData} {R : B1.VerifySub.VsRunC} {κ : ℕ} {L : MemImage κ}
    {fr : Frames} {args : List E} {Wi : Inst} {kv : Memory.Tree} {ν : ℕ → String → Val → V → E}
    (hWt : Wi.t = kv.retemp coreProgram B2C.fs ν Wi.fp)
    (hVs : B1.VerifySub.VsRootTreeE S OsQ End.bytecode D R B2C.fs B2C.cert Wi.fp kv)
    (hvW : ∃ args' rets', Wi.t.ValidB S coreProgram L.read args' rets')
    (hfr : fr "verify_sub" args = some Wi.fp)
    (hbody : Located.BodyAtB Sd L "verify_sub" args [] Wi.fp)
    (hag : B2C.NodeAgree Wi.t (Located.valAt L "verify_sub" Wi.fp))
    (hld : ∀ q ∈ kv.loadEqns coreProgram, L.read q.1 = some q.2)
    (hO : ∀ σv bufs ks, kv = .node "verify_sub" σv bufs ks →
      Located.wOLB Sd fr L (openName (B1.VerifySub.vsLayout End.bytecode σv).stackLog
        (B1.VerifySub.vsRate σv)) (B1.VerifySub.vsOpenArgs σv) (B1.VerifySub.vsOpenRets σv) = D.os) :
    Located.wVsLB Sd fr L args [] = D.proof := by
  obtain ⟨σv, bufsv, ksv, rfl, -, -, -⟩ := id hVs
  unfold Located.wVsLB Located.frameDecB
  rw [Located.frameOfB_of_bodyAt hfr hbody]
  beta_reduce
  have hWt' := hWt
  rw [retemp_node] at hWt'
  obtain ⟨args', rets', hv⟩ := hvW
  rw [hWt'] at hv
  obtain ⟨fn, hf, -, es, vs, hw, -⟩ := hv
  have hcf : coreProgram.find? "verify_sub" = some (coreOf 16) := by
    rw [coreOf_16]; exact B1.VerifySub.find_verify_sub
  obtain rfl : fn = coreOf 16 := Option.some.inj (hf.symm.trans hcf)
  rw [hWt'] at hag
  rw [vsProofOf_of_agree hag hw, vsProofOf_congr End.bytecode L.read _ fun v hv =>
    retempVal_uses coreProgram_fresh B1.VerifySub.find_verify_sub (vsProofVars_uses v hv)]
  exact B1.VerifySub.vsProofOf_eq_proofE hVs L.read hld _ (hO σv bufsv ksv rfl)

section Honest

variable {S : BlakeSem} (hfun : B2C.SemFunctional S)
  (hcan : ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
    CanonicalCells m cv0 cv1 o0 o1 md)
  {hdr : E × E} {rd : Reader} {T0 : Memory.Tree} {ν : ℕ → String → Val → V → E}
  (hname : (T0.retemp coreProgram B2C.fs ν 0).name = "main")
  (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0) B2C.cert
    rd [] [])
  {n : ℕ} (hrun : runB S guest (honest coreProgram B2C.fs B2C.H B2C.C hdr
    (T0.retemp coreProgram B2C.fs ν 0)) n Regs.initial = some (Regs.final guest))

include hfun hcan hname hH hrun in
set_option maxHeartbeats 1000000 in
/-- **Child `c`'s `verify_sub` instance**: the re-chosen tree of its iteration's callee `kv`
(satisfying `VsQ` at child `c`'s run), with V_I's argument words, its body holding at its frame
under the honest run's table, the decoder's valuation there agreeing with it. -/
theorem vs_child_inst {W : B1.Main.MainWords} {rd0 : Reader} {σ0 : Val} {bufs : List ℕ}
    {ks : List Memory.Tree} (hT0 : T0 = .node "main" σ0 bufs ks)
    (hσ0 : σ0 = B1.Main.mainVal rd0 (B1.Main.mainRunAt B2C.fs 0 W))
    {VsQ : B1.VerifySub.VsData → B1.VerifySub.VsRunC → ℕ → Reader → Memory.Tree → Prop}
    (hVsQ : ∀ D R b rd t, VsQ D R b rd t → ∃ σ bufs ks, t = .node "verify_sub" σ bufs ks)
    {vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC}
    {CQ SQ : List E → List E → ℕ → Reader → Memory.Tree → Prop} {LQ : List E → ℕ → Reader → Memory.Tree → Prop}
    {nc : ℕ} (hQ : B1.Main.MainQ VsQ vr CQ SQ LQ (B1.Main.mainIQ B2C.fs 0 W) B2C.fs nc 0 σ0 rd0 T0)
    :
    ∃ (b0 : ℕ) (k0 : Memory.Tree),
      B1.Main.Loop5Q VsQ vr CQ SQ LQ (B1.Main.mainIQ B2C.fs 0 W) B2C.fs nc 0 b0 rd0 k0 ∧
    ∀ c < nc, ∃ (kv : Memory.Tree) (Wi : Inst) (σc : Val) (bufsc : List ℕ) (ksc : List Memory.Tree)
      (kc : Memory.Tree), tailN c k0 = .node "__loop5" σc bufsc (ksc ++ [kc]) ∧ ksc[5]? = some kv ∧
      (bases (b0 + c * B2C.fs "__loop5" + B2C.fs "__loop5" + kc.total B2C.fs + bufsc.sum)
        (ksc.map (Memory.Tree.total B2C.fs)))[5]? = some Wi.fp ∧ Wi ∈ honestInsts coreProgram B2C.fs B2C.H hdr (T0.retemp coreProgram B2C.fs ν 0) ∧
      Wi.t = kv.retemp coreProgram B2C.fs ν Wi.fp ∧ VsQ (vr c).1 (vr c).2 Wi.fp rd0 kv ∧
      Wi.t.name = "verify_sub" ∧
      instArgs Wi = vsArgsAt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) c ∧
      Located.BodyAtB (honestSem hdr (T0.retemp coreProgram B2C.fs ν 0) n)
        (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) "verify_sub"
        (vsArgsAt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) c) []
        Wi.fp ∧
      B2C.NodeAgree Wi.t (Located.valAt (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)) "verify_sub" Wi.fp) := by
  set T' := T0.retemp coreProgram B2C.fs ν 0 with hT'
  set L := honest coreProgram B2C.fs B2C.H B2C.C hdr T' with hL
  have hvT : T'.ValidB S coreProgram L.read [] [] := hH.toHonestB.valid_image
  have hgood : ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T', I.GoodB S coreProgram L.read :=
    fun I hI => instsB_good T' 0 hdr hvT I hI
  obtain ⟨R, hR, hRt, hRfp, -⟩ := root_inst (P := coreProgram) (fs := B2C.fs) (H := B2C.H) (hdr := hdr)
    (T := T')
  by_cases hnc : nc = 0
  · subst hnc
    exact ⟨0, .phantom "" (fun _ => 0), trivial, fun c hc => absurd hc (by omega)⟩
  obtain ⟨b, k, J, i, hJ, hJt, hJfp, hRk, -, hL5⟩ :=
    mainQ_loop5_inst (fs := B2C.fs) (ν := ν) hR (by rw [hRt]) hRfp hQ hnc
  -- the exponent tables along the iterations
  let Inv : Inst → Prop := fun I => ∀ σP bufsP kidsP, I.t = .node "__loop5" σP bufsP kidsP →
    B1.ExpTables L.read (σP (.n 16)) (σP (.n 6))
  have hInvJ : Inv J := fun σP bufsP kidsP hPt =>
    honest_exp_root hfun hcan hname hH hrun hR hRt hRfp hRk hPt
  have hInv : ∀ I ∈ T'.insts B2C.fs coreProgram.loop B2C.H 0 hdr,
      ∀ J' ∈ T'.insts B2C.fs coreProgram.loop B2C.H 0 hdr, Inv I →
      ∀ (σ : Val) (bufs : List ℕ) (ks : List Memory.Tree) (k : Memory.Tree),
      I.t = (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).retemp coreProgram B2C.fs ν I.fp →
      J'.t = k.retemp coreProgram B2C.fs ν (I.fp + B2C.fs "__loop5") →
      J'.fp = I.fp + B2C.fs "__loop5" →
      I.t.kids[ks.length]? = some J'.t → I.kidFps[ks.length]? = some J'.fp → Inv J' := by
    intro I hI J' hJ' hInvI σ bufs ks k hIt hJ't hJ'fp hk hkf σP' bufsP' kidsP' hP't
    rw [retemp_node] at hIt
    have hexp := hInvI _ _ _ hIt
    rcases hgood I hI with ⟨argsI, retsI, hvI⟩ | ⟨f, σf, hph⟩
    · exact honest_exp_loop hIt hvI hexp hk hP't
    · rw [hIt] at hph; cases hph
  refine ⟨b, k, hL5, fun c hc => ?_⟩
  obtain ⟨I', hI', hInvI', hI'fp, σ, bufsI, ksI, kI, htail, hI't, hH5⟩ :=
    loop5Q_insts_pos Inv hInv nc 0 b k hL5 J hJ hJt hJfp hInvJ c hc
  rw [Nat.zero_add] at hH5
  obtain ⟨kv, Wi, hW, hWt, hk5, hkf5, hq, hkv5, hb5⟩ := loop5H_vs_inst_pos hI' hI't hH5
  rw [hI'fp] at hb5
  obtain ⟨σv, bufsv, ksv, rfl⟩ := hVsQ _ _ _ _ _ hq
  have hI't' := hI't
  rw [retemp_node] at hI't'
  have hexp := hInvI' _ _ _ hI't'
  have hWt0 := hWt
  rw [retemp_node] at hWt0
  obtain ⟨σW, kidsW, hWt'⟩ : ∃ σW kidsW, Wi.t = Memory.Tree.node "verify_sub" σW bufsv kidsW :=
    ⟨_, _, hWt0⟩
  -- validity
  obtain ⟨argsI, retsI, hvI⟩ : ∃ argsI retsI, I'.t.ValidB S coreProgram L.read argsI retsI := by
    rcases hgood I' hI' with h | ⟨f, σf, hph⟩
    · exact h
    · rw [hI't'] at hph; cases hph
  have hvW : Wi.t.ValidB S coreProgram L.read ([.n 65, .n 66, .n 13, .n 14, .n 16, .n 6, .n 79].map
      (retempVal coreProgram ν I'.fp "__loop5" σ)) [] := by
    rw [hI't'] at hvI hk5
    exact loop5_vs_valid hvI hk5
  have hbody := honest_vs_bodyAt hfun hcan hname hH hrun hI' hI't' hvI hexp hW hk5 hkf5 hWt' hvW
  have hargs := vsArgsAt_honest (B2C.b2HypsB hfun) hT0 hH hσ0 hI' hI't hH5.1
  rw [← hargs] at hbody hvW
  refine ⟨_, Wi, σ, bufsI, ksI, kI, htail, hkv5, hb5, hW, hWt, hq, by rw [hWt']; rfl, ?_, hbody, ?_⟩
  · -- the instance's argument words are its call's
    rw [hWt'] at hvW
    obtain ⟨fn, hf, hpar, -⟩ := hvW
    have hcf : coreProgram.find? "verify_sub" = some (coreOf 16) := by
      rw [coreOf_16]; exact B1.VerifySub.find_verify_sub
    obtain rfl : fn = coreOf 16 := Option.some.inj (hf.symm.trans hcf)
    unfold instArgs
    rw [hWt']
    simp only [Memory.Tree.name, Memory.Tree.val, idxOf_vs]
    exact hpar
  · -- the decoder's valuation at the frame agrees with the instance
    intro j hj es vs hw v hv h2 hn
    rw [hWt'] at hj hw ⊢
    exact honest_valAt hfun hname hH hW hWt' hj hw hv h2 hn

end Honest

end
end LeanVM.E2E.Complete
