/-
  LeanVM.E2E.Complete.DecodeOpen

  The openings' frames on the honest memory: V_I's frame valuations agree with the honest
  instances of the openings' decoded callees.
-/

module

public import LeanVM.E2E.Complete.DecodeD3
public import LeanVM.E2E.Complete.DecodeRegions
public import LeanVM.Guest.B1.Comp.Whir.LocT.OsHonest
public import LeanVM.Guest.B1.Comp.VerifySub.PlacedEqO

/-!
# The openings' frames

* `honest_inst_valid`, `honest_nodeAgree`: an honest node instance is valid on the honest memory,
  and the decoder's valuation at its frame agrees with it on its named cells (`honest_valAt`);
* `vagree_honest`: at frames naming every honest instance of a decoded callee (`osDecNames`) in an
  honest instance's subtree, V_I's frame valuations (`frameValsOf`) agree with those instances'
  trees (`VAgree`): the callee's body holds at its frame (`honest_bodyAt_plain`, `osDec_plain`)
  and the decoder's valuation there agrees with it;
* `insts_total`: an instance's subtree lies within its tree's region;
* `open_child`: a child's opening (`VsRootTreeEO`'s `open_stacked` callee) is an honest instance,
  valid on the opening's call words, within its `verify_sub` instance's region, which holds the
  opening's cursor word too.
-/
namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

section Honest

variable {S : BlakeSem} (hfun : B2C.SemFunctional S)
  (hcan : ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
    CanonicalCells m cv0 cv1 o0 o1 md)
  {hdr : E × E} {rd : Reader} {T : Memory.Tree} (hname : T.name = "main")
  (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])
  {n : ℕ} (hrun : runB S guest (honest coreProgram B2C.fs B2C.H B2C.C hdr T) n Regs.initial =
    some (Regs.final guest))

include hH in
/-- The honest instances are valid on the honest memory, or phantoms. -/
theorem honest_inst_valid {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} (ht : I.t = .node f σ bufs kids) :
    ∃ args rets, I.t.ValidB S coreProgram (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read args rets := by
  rcases instsB_good T 0 hdr hH.toHonestB.valid_image I hI with h | ⟨g, σg, hph⟩
  · exact h
  · rw [ht] at hph; cases hph

include hfun hcan hname hH hrun in
set_option maxHeartbeats 1000000 in
/-- **V_I's frame valuations agree with the honest instances of the decoded callees** in an honest
instance's subtree, at frames naming them. -/
theorem vagree_honest {fr : Frames} {J : Inst} (hJ : J ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    (hfr : ∀ K ∈ J.t.insts B2C.fs coreProgram.loop B2C.H J.fp J.hdr, K.t.name ∈ B1.osDecNames →
      fr K.t.name (instArgs K) = some K.fp) :
    B1.VAgree (B1.frameValsOf (honestSem hdr T n) fr (honest coreProgram B2C.fs B2C.H B2C.C hdr T))
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
  have hbody := honest_bodyAt_plain (n := n) hfun hcan hname hH hrun hKT hKt hj hj1 ⟨hp, hm, hs⟩
    (by rw [hKt]; exact hkv')
  unfold B1.frameValsOf
  rw [Located.frameOfB_of_bodyAt hfrK hbody]
  intro j' hj' es' vs' hw' v hv h2 hn
  exact honest_valAt hfun hname hH hKT hKt hj' hw' hv h2 hn


include hfun hname hH in
/-- **The decoder's valuation at an honest frame agrees with the instance** on its named cells. -/
theorem honest_nodeAgree {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} (ht : I.t = .node f σ bufs kids) :
    B2C.NodeAgree I.t (Located.valAt (honest coreProgram B2C.fs B2C.H B2C.C hdr T) f I.fp) := by
  intro j hj es vs hw v hv h2 h3
  rw [ht] at hj hw ⊢
  exact honest_valAt hfun hname hH hI ht hj hw hv h2 h3

end Honest


section Within

variable {fs : String → ℕ} {lp : String → Bool} {H : Inst → ℕ → E × E}

mutual
/-- **An instance's subtree lies within its tree's region.** -/
theorem insts_total : ∀ (t : Memory.Tree) (fp : ℕ) (hdr : E × E), ∀ I ∈ t.insts fs lp H fp hdr,
    fp ≤ I.fp ∧ I.fp + I.t.total fs ≤ fp + t.total fs
  | .node f σ bufs kids, fp, hdr, I, hI => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact ⟨le_rfl, le_rfl⟩
      · have h := instsKids_total kids _ _ 0 fp (fp + (Memory.Tree.node f σ bufs kids).total fs)
          (fun q hq => by
            have := kidPos_regions (fs := fs) (lp := lp) fp f bufs _ q hq
            rw [total_node, totalKids_eq_sum]
            omega) I hI
        exact h
  | .phantom f σ, fp, hdr, I, hI => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      exact ⟨le_rfl, le_rfl⟩

/-- `insts_total` for the callees at `ps`, within `[lo, hi)`. -/
theorem instsKids_total : ∀ (ks : List Memory.Tree) (ps : List ℕ) (I : Inst) (j : ℕ) (lo hi : ℕ),
    (∀ q ∈ (ks.map (Memory.Tree.total fs)).zip ps, lo ≤ q.2 ∧ q.2 + q.1 ≤ hi) →
    ∀ J ∈ Memory.Tree.instsKids fs lp H I j ps ks, lo ≤ J.fp ∧ J.fp + J.t.total fs ≤ hi
  | [], _, _, _, _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, _, _, _, J, hJ => by
      rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, p :: ps, I, j, lo, hi, hq, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · have h1 := insts_total k p (H I j) J hJ
        have h2 := hq (k.total fs, p) (by simp)
        simp only at h2
        omega
      · exact instsKids_total ks ps I (j + 1) lo hi
          (fun q hq' => hq q (by simp only [List.map_cons, List.zip_cons_cons]; exact List.mem_cons_of_mem _ hq'))
          J hJ
end

end Within


set_option maxRecDepth 100000 in
theorem vsOpenVars_uses : ∀ v ∈ [V.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726, .n 1648, .n 1649,
    .n 1650, .n 1651], v ∈ Stmt.usesList (Fn.body Data.core15) := by
  decide +kernel

section Open

variable {S : BlakeSem} {hdr : E × E} {rd : Reader} {T : Memory.Tree}
  (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])

include hH in
set_option maxHeartbeats 1000000 in
/-- **A child's opening, as an honest instance**: the `open_stacked` callee `ko` of a
`verify_sub` instance whose tree decodes the run (`VsRootTreeEO`) is an honest instance `J` of its
re-chosen tree, a callee of the instance, valid on the opening's call words, in the instance's
region; the opening's cursor word is in the instance's region. -/
theorem open_child {OsQ : ℕ → ℕ → List Opening → ℕ → Memory.Tree → Prop}
    {D : B1.VerifySub.VsData} {R : B1.VerifySub.VsRunC} {Wi : Inst} {kv : Memory.Tree}
    {ν : ℕ → String → Val → V → E}
    (hW : Wi ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    (hWt : Wi.t = kv.retemp coreProgram B2C.fs ν Wi.fp)
    (hEO : B1.VerifySub.VsRootTreeEO S OsQ End.bytecode D R B2C.fs B2C.cert Wi.fp kv) :
    ∃ (σv : Val) (bufsv : List ℕ) (ksv : List Memory.Tree) (ko : Memory.Tree) (J : Inst) (a : ℕ),
      kv = .node "verify_sub" σv bufsv ksv ∧ ko ∈ ksv ∧
      B1.VerifySub.VsFrame End.bytecode D R B2C.fs Wi.fp σv ∧
      (∃ b, OsQ (B1.VerifySub.layoutOf End.bytecode D.logMem D.rows).stackLog D.rate D.os b ko) ∧
      J ∈ honestInsts coreProgram B2C.fs B2C.H hdr T ∧ J.t = ko.retemp coreProgram B2C.fs ν J.fp ∧
      J.t.name = B1.VerifySub.openName (B1.VerifySub.vsLayout End.bytecode σv).stackLog
        (B1.VerifySub.vsRate σv) ∧
      J.t.ValidB S coreProgram (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read
        (B1.VerifySub.vsOpenArgs σv) (B1.VerifySub.vsOpenRets σv) ∧
      (B1.VerifySub.vsOpenArgs σv)[5]? = some (ofK (Parameters.gpow a)) ∧
      Wi.fp ≤ a ∧ a < Wi.fp + Wi.t.total B2C.fs ∧
      Wi.fp ≤ J.fp ∧ J.fp + J.t.total B2C.fs ≤ Wi.fp + Wi.t.total B2C.fs := by
  obtain ⟨σv, bufsv, ksv, rfl, hfr, -, ⟨a, ha5, ha1, ha2⟩, ko, hko, b, hos, -, -, i, sel, hki, hwv, hci⟩ :=
    hEO
  have hWt' := hWt
  rw [retemp_node] at hWt'
  have hi : i < (kidPos B2C.fs coreProgram.loop Wi.fp "verify_sub" bufsv
      (ksv.map (Memory.Tree.total B2C.fs))).length := by
    rw [length_kidPos, List.length_map]; exact (List.getElem?_eq_some_iff.mp hki).1
  obtain ⟨p, hp⟩ : ∃ p, (kidPos B2C.fs coreProgram.loop Wi.fp "verify_sub" bufsv
      (ksv.map (Memory.Tree.total B2C.fs)))[i]? = some p := ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨J, hJ, hJt, hJp, hWk, -⟩ := retemp_kid_inst hW hWt hki hp
  -- the instance's validity, its callee's
  obtain ⟨argsW, retsW, hvW⟩ := honest_inst_valid hH hW hWt'
  rw [hWt'] at hvW
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hvW
  obtain rfl : fn = Data.core15 := Option.some.inj (hf.symm.trans B1.VerifySub.find_verify_sub)
  rw [walk_retemp coreProgram_fresh B1.VerifySub.find_verify_sub, hwv] at hw
  obtain ⟨rfl, -⟩ := Out.ret.inj hw
  obtain ⟨-, hget⟩ := B2C.kidsValidB_get hkv
  obtain ⟨k', hk', hkn, hkval⟩ := hget i _ hci
  rw [hWt'] at hWk
  have hkk : k' = J.t := Option.some.inj (hk'.symm.trans hWk)
  subst hkk
  have hvJ := hkval rfl
  have hu : ∀ v ∈ [V.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726, .n 1648, .n 1649, .n 1650, .n 1651],
      retempVal coreProgram ν Wi.fp "verify_sub" σv v = σv v := fun v hv =>
    retempVal_uses coreProgram_fresh B1.VerifySub.find_verify_sub (vsOpenVars_uses v hv)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hu
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10⟩ := hu
  simp only [List.map_cons, List.map_nil, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10] at hvJ
  -- the opening's region within the instance's
  have hreg : Wi.fp ≤ J.fp ∧ J.fp + J.t.total B2C.fs ≤ Wi.fp + Wi.t.total B2C.fs := by
    have hq : (ko.total B2C.fs, p) ∈ (ksv.map (Memory.Tree.total B2C.fs)).zip
        (kidPos B2C.fs coreProgram.loop Wi.fp "verify_sub" bufsv (ksv.map (Memory.Tree.total B2C.fs))) := by
      refine List.mem_iff_getElem?.mpr ⟨i, ?_⟩
      rw [List.getElem?_zip_eq_some]
      exact ⟨by rw [List.getElem?_map, hki]; rfl, hp⟩
    have := kidPos_regions (fs := B2C.fs) (lp := coreProgram.loop) Wi.fp "verify_sub" bufsv _ _ hq
    rw [hJt, total_retemp, hJp, hWt, total_retemp, total_node, totalKids_eq_sum]
    simp only at this
    omega
  refine ⟨σv, bufsv, ksv, ko, J, a, rfl, hko, hfr, ⟨b, hos⟩, hJ, by rw [hJt, hJp], ?_, hvJ, ha5, ha1,
    by rw [hWt, total_retemp]; exact ha2, hreg⟩
  exact hkn

end Open

end
end LeanVM.E2E.Complete
