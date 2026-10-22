/-
  LeanVM.E2E.Complete.DecodePad

  D3 on the zero-padded honest memory: V_I's decoder reads each child's proof off any extension of
  the honest memory, at the frames naming the honest instances.
-/

module

public import LeanVM.E2E.Complete.HonestBodiesPad
public import LeanVM.E2E.Complete.DecodeFinal

/-!
# The children's proofs, decoded off the padded memory

`d3HypO`'s proof (`DecodeFinal.lean`) with the decoder reading an extension `L'` of the honest
memory (`MemExt`, `PadHonest.lean`; the zero padding, of `2^κ'` words, `16 ≤ κ' ≤ 32`): the
instances, their regions and the frames naming them are the honest memory's; their bodies hold on
`L'` (`HonestBodiesPad.lean`); the decoder's valuations and `verify_sub`'s argument words are
equal on `L'` (they read with the default `0`); the evaluations and the load equations read alike.

* `vsArgsAt_ext`, `honest_inst_valid_ext`;
* `vs_child_inst_ext`, `vagree_ext`, `honest_nodeAgree_ext`: `vs_child_inst`, `vagree_honest`,
  `honest_nodeAgree` with the bodies and valuations on `L'`;
* **`d3HypO_ext`**: frames at which V_I's decoder reads each child's proof off `L'`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Node LeanVM.Protocol.LeanIsa
open LeanVM.Guest.B1.Main (calleeBd vsExtLR VsGoodC honestWordsC mainIn mainVal mainRunAt mainIQ MainQ
  calleesAtC_of_open)

@[expose] public section

/-- `verify_sub`'s argument words as the decoder reads them are equal on an extension. -/
theorem vsArgsAt_ext {κ κ' : ℕ} {L : MemImage κ} {L' : MemImage κ'} (hX : MemExt L L') (c : ℕ) :
    vsArgsAt L' c = vsArgsAt L c := by
  simp only [vsArgsAt, mainFrame, hX.valG, B1.Main.cellAt, hX.getD]

section HonestT

variable {S : BlakeSem} (hfun : B2C.SemFunctional S)
  (hcan : ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
    CanonicalCells m cv0 cv1 o0 o1 md)
  {hdr : E × E} {rd : Reader} {T : Memory.Tree} (hname : T.name = "main")
  (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])
  {n : ℕ} (hrun : runB S guest (honest coreProgram B2C.fs B2C.H B2C.C hdr T) n Regs.initial =
    some (Regs.final guest))
  {κ' : ℕ} {L' : MemImage κ'} (hX : MemExt (honest coreProgram B2C.fs B2C.H B2C.C hdr T) L')
  (h16' : minLogMem ≤ κ') (h32' : κ' ≤ maxLogMem)

include hH hX in
/-- The honest instances are valid on the extension, or phantoms (`honest_inst_valid`). -/
theorem honest_inst_valid_ext {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} (ht : I.t = .node f σ bufs kids) :
    ∃ args rets, I.t.ValidB S coreProgram L'.read args rets := by
  rcases instsB_good T 0 hdr (hX.validB hH.toHonestB.valid_image fun _ hq ↦ hH.toHonestB.read_eqn hq)
    I hI with h | ⟨g, σg, hph⟩
  · exact h
  · rw [ht] at hph; cases hph

include hfun hcan hname hH hrun hX h16' h32' in
set_option maxHeartbeats 1000000 in
/-- **V_I's frame valuations on the extension agree with the honest instances of the decoded
callees** (`vagree_honest`). -/
theorem vagree_ext {fr : Frames} {J : Inst} (hJ : J ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    (hfr : ∀ K ∈ J.t.insts B2C.fs coreProgram.loop B2C.H J.fp J.hdr, K.t.name ∈ B1.osDecNames →
      fr K.t.name (instArgs K) = some K.fp) :
    B1.VAgree (B1.frameValsOf (honestSem hdr T n) fr L')
      (J.t.insts B2C.fs coreProgram.loop B2C.H J.fp J.hdr) := by
  intro I hI f σ bufs kids hIt i c k hc hk ht hfn
  have hIT : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T := insts_sub T 0 hdr J hJ I hI
  obtain ⟨argsI, retsI, hvI⟩ := honest_inst_valid hH hIT hIt
  have hvI' := hvI
  rw [hIt] at hvI'
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hvI'
  have hev : I.t.events coreProgram = es := by rw [hIt]; exact events_node hf hw
  rw [hev] at hc
  obtain ⟨-, hget⟩ := B2C.kidsValidB_get hkv
  obtain ⟨k', hk', hkn, hkval⟩ := hget i c hc
  have hkk : k = k' := Option.some.inj (hk.symm.trans hk')
  subst hkk
  have hkv' := hkval ht
  -- the callee's instance
  have hkI : I.t.kids[i]? = some k := by rw [hIt]; exact hk
  obtain ⟨K, hK, hKt, hKf, -⟩ := insts_kid J.t J.fp J.hdr I hI i k hkI
  have hKT : K ∈ honestInsts coreProgram B2C.fs B2C.H hdr T := insts_sub T 0 hdr J hJ K hK
  obtain ⟨σk, bk, kk, rfl⟩ : ∃ σk bk kk, k = Memory.Tree.node c.f σk bk kk := by
    rcases k with ⟨g, σk, bk, kk⟩ | ⟨g, σk⟩
    · have : g = c.f := hkn
      exact ⟨σk, bk, kk, by rw [this]⟩
    · exact hkv'.elim
  obtain ⟨j, hj, hj1, hp, hm, hs⟩ := B1.osDec_plain c.f (List.mem_append_left _ hfn)
  -- the callee's argument words
  have hargs : instArgs K = c.args.map σ := by
    obtain ⟨fk, hfk, hpar, -⟩ := hkv'
    obtain ⟨i', hji, hi', hnm, hfi, hco, -⟩ := B2C.fn_of_idx hj
    obtain rfl : fk = coreOf j := Option.some.inj (hfk.symm.trans (by rw [hfi, hco]))
    unfold instArgs
    rw [hKt]
    simp only [Memory.Tree.name, Memory.Tree.val, hj]
    exact hpar
  have hfrK := hfr K hK (by rw [hKt]; exact hfn)
  rw [hargs, hKt] at hfrK
  simp only [Memory.Tree.name] at hfrK
  have hbody := honest_bodyAt_plain_ext (n := n) hfun hcan hname hH hrun hX h16' h32' hKT hKt hj hj1 ⟨hp, hm, hs⟩
    (by rw [hKt]; exact hkv')
  unfold B1.frameValsOf
  rw [Located.frameOfB_of_bodyAt hfrK hbody]
  intro j' hj' es' vs' hw' v hv h2 hn
  exact honest_valAt_ext hfun hname hH hX hKT hKt hj' hw' hv h2 hn


include hfun hname hH hX in
/-- **The decoder's valuation on the extension at an honest frame agrees with the instance**
(`honest_nodeAgree`). -/
theorem honest_nodeAgree_ext {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} (ht : I.t = .node f σ bufs kids) :
    B2C.NodeAgree I.t (Located.valAt L' f I.fp) := by
  intro j hj es vs hw v hv h2 h3
  rw [ht] at hj hw ⊢
  exact honest_valAt_ext hfun hname hH hX hI ht hj hw hv h2 h3

end HonestT

section Honest0

variable {S : BlakeSem} (hfun : B2C.SemFunctional S)
  (hcan : ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
    CanonicalCells m cv0 cv1 o0 o1 md)
  {hdr : E × E} {rd : Reader} {T0 : Memory.Tree} {ν : ℕ → String → Val → V → E}
  (hname : (T0.retemp coreProgram B2C.fs ν 0).name = "main")
  (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0) B2C.cert
    rd [] [])
  {n : ℕ} (hrun : runB S guest (honest coreProgram B2C.fs B2C.H B2C.C hdr
    (T0.retemp coreProgram B2C.fs ν 0)) n Regs.initial = some (Regs.final guest))
  {κ' : ℕ} {L' : MemImage κ'}
  (hX : MemExt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) L')
  (h16' : minLogMem ≤ κ') (h32' : κ' ≤ maxLogMem)

include hfun hcan hname hH hrun hX h16' h32' in
set_option maxHeartbeats 1000000 in
/-- **Child `c`'s `verify_sub` instance, its body on the extension** (`vs_child_inst`, the body
and the decoder's valuation on `L'`). -/
theorem vs_child_inst_ext {W : B1.Main.MainWords} {rd0 : Reader} {σ0 : Val} {bufs : List ℕ}
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
      Located.BodyAtB (honestSem hdr (T0.retemp coreProgram B2C.fs ν 0) n) L' "verify_sub"
        (vsArgsAt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) c) []
        Wi.fp ∧
      B2C.NodeAgree Wi.t (Located.valAt L' "verify_sub" Wi.fp) := by
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
  have hbody := honest_vs_bodyAt_ext hfun hcan hname hH hrun hX h16' h32' hI' hI't' hvI hexp hW hk5 hkf5 hWt' hvW
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
    exact honest_valAt_ext hfun hname hH hX hW hWt' hj hw hv h2 hn

end Honest0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **D3 on an extension of the honest memory** (`d3HypO`): frames at which V_I's decoder reads
each child's proof off `L'`. -/
theorem d3HypO_ext (CM : CompModel) (Ht : Compile.Bytes → Digest) (seed : Digest) (s : NodeStatement)
    (w : NodeWitness) (vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC) (hdr : E × E)
    (rd0 : Reader) (T0 : Memory.Tree) (ν : ℕ → String → Val → V → E) (n : ℕ)
    (hvr : ∀ c, VrP CM Ht seed w c (vr c))
    (hn' : (T0.retemp coreProgram B2C.fs ν 0).name = "main")
    (hQ : MainQ (fun D R b _ t => B1.VerifySub.VsRootTreeEO CM.sem B1.OsQ End.bytecode D R B2C.fs B2C.cert b t) vr
      (CclQP CM.H) (SdQP CM.H) B1.Main.Loop100Q (mainIQ B2C.fs 0 (honestWordsC Ht seed s w)) B2C.fs
      w.children.length 0 (mainVal rd0 (mainRunAt B2C.fs 0 (honestWordsC Ht seed s w))) rd0 T0)
    (hH : HonestAtB CM.sem coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0) B2C.cert
      (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read [] [])
    (hrun : runB CM.sem guest (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) n
      Regs.initial = some (Regs.final guest))
    (hbase6 : B1.Main.mainBase B2C.fs 0 (honestWordsC Ht seed s w) 6 ≤ 2 ^ 32)
    (hnc16 : w.children.length ≤ 16)
    {κ' : ℕ} {L' : MemImage κ'}
    (hX : MemExt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) L')
    (h16' : minLogMem ≤ κ') (h32' : κ' ≤ maxLogMem) :
    ∃ fr : Frames, ∀ c (hc : c < w.children.length),
      Located.wVsLB (honestSem hdr (T0.retemp coreProgram B2C.fs ν 0) n) fr L' (vsArgsAt L' c) [] =
        w.children[c].proof := by
  have hfun : B2C.SemFunctional CM.sem := fun h h' => CM.functional h h'
  have hcan := @CM.canonical
  obtain ⟨bufs, ks, hT0, -⟩ := id hQ
  obtain ⟨b0, k0, hL5, hch⟩ := vs_child_inst_ext hfun hcan hn' hH hrun hX h16' h32' hT0 rfl
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
  rw [vsArgsAt_ext hX]
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
  have hbJ := honest_bodyAt_plain_ext (n := n) hfun hcan hn' hH hrun hX h16' h32' (hJm c hc) hJt' hjJ hjJ1 ⟨hpJ, hmJ, hsJ⟩
    (hJv c hc)
  have hfrJ : frOf Is (B1.VerifySub.openName (B1.VerifySub.vsLayout End.bytecode (σv c hc)).stackLog
      (B1.VerifySub.vsRate (σv c hc))) (B1.VerifySub.vsOpenArgs (σv c hc)) = some (Jf c hc).fp := by
    rw [← hJargs c hc, ← hJn c hc]
    exact frOf_eq (Or.inr (Or.inl ⟨c, hc, rfl⟩)) fun I' hI' => hU _ I' (Or.inr (Or.inl ⟨c, hc, rfl⟩)) hI'
  -- the openings decode
  have hO : ∀ σ' bufs' ks', kvf c hc = .node "verify_sub" σ' bufs' ks' →
      Located.wOLB (honestSem hdr (T0.retemp coreProgram B2C.fs ν 0) n) (frOf Is) L'
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
    refine hos _ (B1.frameValsOf (honestSem hdr (T0.retemp coreProgram B2C.fs ν 0) n) (frOf Is) L') _
      ?_ ?_ ?_
    · intro q hq
      have hq' : q ∈ (Jf c hc).t.loadEqns coreProgram := by
        rw [hJt c hc, loadEqns_retemp coreProgram_fresh]; exact hq
      exact hX.read _ _ (honest_read_inst hH.toHonestB (hJm c hc) q hq')
    · obtain ⟨J0, rest, hJ0, hJ0t, hJ0fp, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop)
        (H := B2C.H) (Jf c hc).t (Jf c hc).fp (Jf c hc).hdr
      refine B1.kidsLink_of_vagree (ν := ν) (vagree_ext hfun hcan hn' hH hrun hX h16' h32' (hJm c hc)
        fun K hK hKn => frOf_eq (Or.inr (Or.inr ⟨c, hc, hK, hKn⟩))
          fun I' hI' => hU _ I' (Or.inr (Or.inr ⟨c, hc, hK, hKn⟩)) hI') (ko c hc) J0
        (by rw [hJ0]; exact List.mem_cons_self) (by rw [hJ0t, hJ0fp]; exact hJt c hc)
    · refine B1.nodeAgree_of_retemp (ν := ν) (fp := (Jf c hc).fp) ?_
      rw [← hJt c hc]
      have hJt2 := hJt'
      rw [(hfrm c hc).layout, (hfrm c hc).rate] at hJt2
      exact honest_nodeAgree_ext hfun hn' hH hX (hJm c hc) hJt2
  -- the proof
  have hvW : ∃ args' rets', (Wf c hc).t.ValidB CM.sem coreProgram L'.read args' rets' := by
    have hWt' := hWt c hc
    rw [hkv c hc, retemp_node] at hWt'
    exact honest_inst_valid_ext hH hX (hWm c hc) hWt'
  have hld : ∀ q ∈ (kvf c hc).loadEqns coreProgram, L'.read q.1 = some q.2 := by
    intro q hq
    have hq' : q ∈ (Wf c hc).t.loadEqns coreProgram := by
      rw [hWt c hc, loadEqns_retemp coreProgram_fresh]; exact hq
    exact hX.read _ _ (honest_read_inst hH.toHonestB (hWm c hc) q hq')
  rw [vs_proof_of_inst (hWt c hc) (hq c hc).toE hvW hfrW (hWb c hc) (hWag c hc) hld hO]
  exact ((hvr c) hc).2.2.2.2

end
end LeanVM.E2E.Complete
