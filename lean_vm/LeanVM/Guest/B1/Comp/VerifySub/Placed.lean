/-
  LeanVM.Guest.B1.Comp.VerifySub.Placed

  `verify_sub` complete in the uniform placed form within weights over a completeness model, at a
  run record, its tree's frame decoding back the run's proof stream, public input and seed.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.PlacedKids

/-!
# `verify_sub` is complete, placed, over a completeness model

`verify_sub_completeAtWC`: `CPlaced8.lean`'s `verify_sub_completeAtW` over a `CompModel`, at a
run record `R` the model answers (`R.Ans CM D`), the run within the limits over the model
(`D.OkC CM bytecode R`), the tables' context (`D.TOk`) and the cap's agreement `CapOk` at the run
record's batching state and target: at every frame pointer one tree of one size serves every
memory holding `verify_sub`'s buffers, its callees' and the caller's words it reads
(`vsExtLC`: the exponent tables and `defer_out`'s cells at the run record's claims), within the
weights at every `w θ` under `CM.sem`.

The tree is the node of `verify_sub` at the frame pointer (`CompleteAtWSRoot`), its valuation
decoding back the run (`VsDecodes`): the public input and seed of its argument cells
(`vsPiOf`, `vsSeedOf`), the announced layout and rate (`vsLayout`, `vsRate`), and the child
proof's stream (`streamAt` at `σ 14` of `vsStreamLen` words) is `D.stream`; the dispatched
opening is `open_stacked` at the run's configuration on the run record's batching state and
target, so `vsProofOf` reads `⟨D.stream, wO … ⟩` (`vsProofOf_of_decodes`), the openings those of
the opening's frame (whose own decoding the opening's placed completeness states).

`verify_sub_completeAtWSC` forgets the root; `…_of_comp` recovers the deployed
`verify_sub_completeAtW` at `CompModel.deployed`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The placed form with the node's valuation -/

section Root

variable {S : BlakeSem} (fs : String → ℕ) (cert : String → V → ℕ) {Θ : Type} (w : Θ → String → ℕ)

variable (S) in
/-- **`RelAtInWS` by a node of `f` whose valuation satisfies `Q`.** -/
def RelAtInWSRoot (rd : Reader) (R D : ℕ → Prop) (fp n : ℕ) (f : String) (args rets : List E)
    (Bw : Θ → ℕ) (Q : Val → Prop) : Prop :=
  ∃ (σ : Val) (bufs : List ℕ) (ks : List Tree), Q σ ∧
    let t := Memory.Tree.node f σ bufs ks
    t.ValidB S coreProgram rd args rets ∧ t.BufsOk coreProgram ∧
    t.Placed coreProgram fs cert fp ∧ t.total fs = n ∧ t.LoadsIn coreProgram fs cert R fp ∧
    (∀ i, D i → t.Data coreProgram fs cert fp i) ∧ ∀ θ, t.weight (w θ) ≤ Bw θ

variable (S) in
/-- **`CompleteAtWS` by nodes whose valuation satisfies `Q fp rd`** at the frame pointer `fp` on the
memory `rd`. -/
def CompleteAtWSRoot (κ : ℕ) (f : String) (Lin : Main.Layout) (args : List E)
    (Out : List E → Main.Layout → Prop) (B : ℕ) (Bw : Θ → ℕ) (Q : ℕ → Reader → Val → Prop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Main.Layout) (rets : List E) (Lout : Main.Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ n ≤ B ∧ ∀ rd, LowDef κ rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInWSRoot S fs cert w rd (RegionL Lin) (RegionL Lout) fp n f args rets Bw (Q fp rd)

variable {fs cert w}

theorem RelAtInWSRoot.toWS {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Bw : Θ → ℕ} {Q : Val → Prop} (h : RelAtInWSRoot S fs cert w rd R D fp n f args rets Bw Q) :
    Main.RelAtInWS S fs cert w rd R D fp n f args rets Bw :=
  let ⟨_, _, _, _, hv, hb, hp, ht, hl, hd, hw⟩ := h
  ⟨_, rfl, hv, hb, hp, ht, hl, hd, hw⟩

theorem CompleteAtWSRoot.toWS {κ : ℕ} {f : String} {Lin : Main.Layout} {args : List E}
    {Out : List E → Main.Layout → Prop} {B : ℕ} {Bw : Θ → ℕ} {Q : ℕ → Reader → Val → Prop}
    (h : CompleteAtWSRoot S fs cert w κ f Lin args Out B Bw Q) :
    Main.CompleteAtWS S fs cert w κ f Lin args Out B Bw := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm => (hr rd hl hm).toWS⟩

variable {rd : Reader} {σ : Val}

/-- **`relAtInWS_of_walk` naming the node** (`Main.relAtInWS_of_walk`): the tree is the node of
`f` at `σ`. -/
theorem relAtInWS_of_walk_root {R D Dk : ℕ → Prop} {fp N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Memory.Ev} {vs : List V} {bws : List (Θ → ℕ)}
    {Q : Val → Prop} (hQ : Q σ)
    (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false ∨ calls es = []) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.HoldsB S rd σ)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f) (allocs σ es)).map fun b => ofK (Parameters.gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (Parameters.gpow (fp + cert f q.2)))
    (hk : Main.KidsFromInWS S fs cert w rd σ
      (fun i => R i ∨ ownData cert fp (fp + fs f) f (allocs σ es) es i)
      (fun _ => False) (calls es) bws (fp + fs f + (allocs σ es).sum) N Dk)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = Parameters.gpow i ∧
      (ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ R i ∨ Dk i))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ Dk i) :
    RelAtInWSRoot S fs cert w rd R D fp (fs f + (allocs σ es).sum + N) f args rets
      (fun θ => w θ f + (bws.map (· θ)).sum) Q := by
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl, hkw⟩ :=
    Main.kidsS_of_kidsFromInW _ _ _ _ _ _ _
      (takes_of_calls coreProgram_wf (List.mem_of_find?_eq_some hf) hw) hk
  have hl' : coreProgram.loop f = false ∨ ks.map (Tree.total fs) = [] := by
    rcases hl with hl | hl
    · exact Or.inl hl
    · rw [hl] at hkv
      cases ks with
      | nil => exact Or.inr rfl
      | cons _ _ => exact hkv.elim
  obtain ⟨hbb, hkpos⟩ := kidPos_not_loop (P := coreProgram) (fs := fs) (fp := fp) (bufs := allocs σ es) hl'
  have hdata : ∀ i, (Memory.Tree.node f σ (allocs σ es) ks).Data coreProgram fs cert fp i ↔
      ownData cert fp (fp + fs f) f (allocs σ es) es i ∨
        Tree.DataKids coreProgram fs cert (bases (fp + fs f + (allocs σ es).sum) (ks.map (Tree.total fs))) ks i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos]
  refine ⟨σ, allocs σ es, ks, hQ, ⟨fn, hf, hp, es, vs, hw, hr, hes, hkv⟩, ?_, ?_, ?_, ?_, ?_,
    fun θ => by have := hkw θ; simp only [Tree.weight]; omega⟩
  · rw [Tree.BufsOk, events_node hf hw]
    exact ⟨rfl, hkb⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    exact ⟨⟨hbuf, haddr⟩, hkp⟩
  · rw [total_node, totalKids_eq_sum, hks]
    omega
  · rw [loadsIn_node, events_node hf hw, hkpos]
    refine ⟨fun A hA => ?_, hkl _ (fun i hi => ?_) (fun _ h => h.elim) (fun i hi => ?_)⟩
    · obtain ⟨i, hi, h⟩ := hload A hA
      refine ⟨i, hi, ?_⟩
      rw [hdata]
      rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact (hkd i h).elim (fun h => h.elim) fun h => Or.inl (Or.inr h)
    · rcases hi with h | h
      · exact Or.inr h
      · exact Or.inl ((hdata i).mpr (Or.inl h))
    · exact Or.inl ((hdata i).mpr (Or.inr hi))
  · intro i hi
    rw [hdata]
    rcases hD i hi with h | h
    · exact Or.inl h
    · exact (hkd i h).elim (fun h => h.elim) fun h => Or.inr h

/-- At the deployed semantics, `RelAtInWSRoot` gives the deployed `RelAtInW`. -/
theorem RelAtInWSRoot.toW_deployed {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Bw : Θ → ℕ} {Q : Val → Prop}
    (h : RelAtInWSRoot blakeDeployed fs cert w rd R D fp n f args rets Bw Q) :
    Main.RelAtInW fs cert w rd R D fp n f args rets Bw :=
  relAtInWS_deployed.mp h.toWS

end Root

/-! ## What the node's valuation decodes -/

/-- **`verify_sub`'s valuation decodes the run** at the frame pointer `fp`: the public input and
seed, the announced layout and rate, the proof's stream at `σ 14`, and the dispatched opening's
call on the run record's batching state and target. -/
structure VsDecodes (bytecode : List K) (D : VsData) (R : VsRunC) (fs : String → ℕ) (fp : ℕ)
    (rd : Reader) (σ : Val) : Prop where
  pi : vsPiOf σ = D.pi
  seed : vsSeedOf σ = D.seed
  layout : vsLayout bytecode σ = layoutOf bytecode D.logMem D.rows
  rate : vsRate σ = D.rate
  stream : streamAt rd (σ (.n 14)) (vsStreamLen bytecode σ) = D.stream
  openArgs : vsOpenArgs σ = [(digestScalars R.cvL).1, (digestScalars R.cvL).2, R.target D, D.x0,
    D.x1, curW D (vsPtrsAt fs fp D 0 0 0)]
  openRets : ∃ b, vsOpenRets σ = [D.w.target, ofK (Parameters.gpow b), D.w.inner, D.w.residual]

/-- **The child proof `verify_sub`'s frame decodes**: the run's stream, and the openings the
opening's decoder `wO` reads at the run's configuration on the opening's call. -/
theorem vsProofOf_of_decodes {bytecode : List K} {D : VsData} {R : VsRunC} {fs : String → ℕ}
    {fp : ℕ} {rd : Reader} {σ : Val} (h : VsDecodes bytecode D R fs fp rd σ)
    (wO : String → List E → List E → List Opening) :
    vsProofOf bytecode rd σ wO = ⟨D.stream, wO (openName (layoutOf bytecode D.logMem D.rows).stackLog D.rate)
      [(digestScalars R.cvL).1, (digestScalars R.cvL).2, R.target D, D.x0, D.x1,
        curW D (vsPtrsAt fs fp D 0 0 0)] (vsOpenRets σ)⟩ := by
  simp only [vsProofOf, h.stream, h.layout, h.rate, h.openArgs]

section Decode

variable {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val} {CM : CompModel} {D : VsData}
  {R : VsRunC} {bytecode : List K}

/-- One atom of the body holds under `S`, whatever the calls hold of. -/
theorem vsBody_atomB (h : Stmt.HoldsListB S C rd σ vsBody True fun rs => rs = []) (n : ℕ)
    (a : Atom) (heq : stmtsEqb [.atom a] ((vsPre.drop n).take 1) = true) : a.HoldsB S rd σ := by
  rw [← vsPre_eq] at h
  have hsplit : vsPre = vsPre.take n ++ (((vsPre.drop n).take 1) ++ (vsPre.drop n).drop 1) := by
    simp
  have hnr := vsPre_noRet
  rw [hsplit] at h hnr
  rw [noRetList_append, noRetList_append, Bool.and_eq_true, Bool.and_eq_true] at hnr
  rw [holdsListB_append, holdsListB_noRet _ hnr.1, holdsListB_append,
    holdsListB_noRet _ hnr.2.1] at h
  have h1 := h.2.1
  rw [← stmtsEqb_sound heq] at h1
  simpa [Stmt.HoldsListB, Stmt.HoldsB] using h1

/-- **The run's stream has the words its phases read** at the announced sizes. -/
theorem stream_lengthC (hok : D.OkC CM bytecode R) :
    D.stream.length = 10 + (gkrLen (pushDepth (layoutOf bytecode D.logMem D.rows)) +
      (tablesLen (layoutOf bytecode D.logMem D.rows) +
        (flockLen (blake2sR1csLogSize +
          (layoutOf bytecode D.logMem D.rows).tableLogHeights.getD opBlake2s 0) +
          whirLen (layoutOf bytecode D.logMem D.rows).stackLog D.rate))) := by
  have hG := (RunsToM.length_eq hok.gkr (reads_gkrPhase _)).1
  have hT0 := hok.tables (.claimed ⟨D.gr.2.1.take (layoutOf bytecode D.logMem D.rows).logBytecode ++
    R.alphas, D.bv, 0, 0, [], [], [], 0⟩) (bytecodeAtM_claimed _ bytecode)
  have hT := (RunsToM.length_eq hT0 (reads_tablesSeg _ (by
    simp [layoutOf_heights, hok.rows_length, tables_length]) _ _ _ _ _)).1
  have hF0 := hok.flock (.claimed ⟨[], 0, D.alpha, D.zSkip, D.chi.take 8, D.rcs.reverse, D.s, D.mv⟩)
    (matricesAtM_claimed _)
  have hF := (RunsToM.length_eq hF0 (reads_verifyFlock _ _)).1
  have hW := (RunsWithM.length_eq hok.opening (reads_whirOpen _ _ _)).1
  have htau : (layoutOf bytecode D.logMem D.rows).tableLogHeights.getD opBlake2s 0 = D.tau := by
    simp [layoutOf_heights, VsData.tau, VsData.hs, opBlake2s]
  rw [htau]
  simp only [VsData.stream, VsData.tail, List.length_append, List.length_cons, ann_length hok.rows_length,
    hG, hT, hF, hW]
  omega

/-- **The node's valuation decodes the run** (`VsDecodes`): from the values the body leaves
(`vsG11C`), the rows it stores, the honest memory and the opening's call. -/
theorem vsDecodes_of (hok : D.OkC CM bytecode R) {fs : String → ℕ}
    {fp : ℕ} {off kap pt lp sq out : E}
    (hfix : Fixes σ (vsG11C D R (vsPtrsAt fs fp D off kap pt) lp sq out))
    (hbody : Stmt.HoldsListB S C rd σ vsBody True fun rs => rs = [])
    (hm : VsMem0C rd D R (vsPtrsAt fs fp D off kap pt) out)
    (hrets : (σ (.n 1648), σ (.n 1649), σ (.n 1650), σ (.n 1651)) = (D.w.target, pt, D.w.inner,
      D.w.residual)) (hpt : ∃ b, pt = ofK (Parameters.gpow b)) :
    VsDecodes bytecode D R fs fp rd σ := by
  set P := vsPtrsAt fs fp D off kap pt
  have e0 : σ (.n 0) = (digestScalars D.pi).1 := hfix.get (by vs_memC)
  have e1 : σ (.n 1) = (digestScalars D.pi).2 := hfix.get (by vs_memC)
  have e2 : σ (.n 2) = (digestScalars D.seed).1 := hfix.get (by vs_memC)
  have e3 : σ (.n 3) = (digestScalars D.seed).2 := hfix.get (by vs_memC)
  have e15 : σ (.n 15) = eOfNat D.logMem := hfix.get (by vs_memC)
  have e121 : σ (.n 121) = eOfNat D.rate := hfix.get (by vs_memC)
  have e30 : σ (.n 30) = P.rows := hfix.get (by vs_memC)
  have e14 : σ (.n 14) = P.stream := hfix.get (by vs_memC)
  have e1171 : σ (.n 1171) = (digestScalars R.cvL).1 := hfix.get (by vs_memC)
  have e1172 : σ (.n 1172) = (digestScalars R.cvL).2 := hfix.get (by vs_memC)
  have e1627 : σ (.n 1627) = R.target D := hfix.get (by vs_memC)
  have e419 : σ (.n 419) = D.x0 := hfix.get (by vs_memC)
  have e434 : σ (.n 434) = D.x1 := hfix.get (by vs_memC)
  have e726 : σ (.n 726) = curW D P := hfix.get (by vs_memC)
  have hrl := hok.rows_length
  have hrows : ∀ t < 6, σ (.n (rdB (t + 1))) = eOfNat (D.rows.getD t 0) := fun t ht => by
    have ha := vsBody_atomB hbody _ _ (vs_rows_blocks t ht)
    simp only [Atom.HoldsB, e30] at ha
    have hr := readsAt_getD hm.rows (k := t) (by simp [hrl]; omega)
    rw [List.getD_eq_getElem _ _ (by simp [hrl]; omega), List.getElem_map,
      ← List.getD_eq_getElem _ 0 (by omega)] at hr
    exact loadHolds_unique ha hr
  have hlm : vsLogMem σ = D.logMem := by
    rw [vsLogMem, e15, kToNat_eOfNat_limb0 (by have := hok.logMem_le; omega)]
  have hra : vsRate σ = D.rate := by
    rw [vsRate, e121, kToNat_eOfNat_limb0 (by have := hok.rate_le; omega)]
  have hro : vsRows σ = D.rows := by
    refine List.ext_getElem (by simp [vsRows, hrl]) fun t h1 h2 => ?_
    have ht : t < 6 := by simpa [vsRows] using h1
    simp only [vsRows, List.getElem_map, List.getElem_range]
    rw [hrows t ht, kToNat_eOfNat_limb0, List.getD_eq_getElem _ _ h2]
    have hlog := hok.rows_log _ (List.getElem_mem (by omega : t < D.rows.length))
    rw [List.getD_eq_getElem _ _ (by omega)]
    have := le_two_pow_log2Ceil (D.rows[t]'(by omega))
    have : 2 ^ log2Ceil (D.rows[t]'(by omega)) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have hlay : vsLayout bytecode σ = layoutOf bytecode D.logMem D.rows := by
    rw [vsLayout, hlm, hro]
  obtain ⟨b, rfl⟩ := hpt
  refine ⟨cellsDigest_eq (by rw [e0, e1]), cellsDigest_eq (by rw [e2, e3]), hlay, hra, ?_, ?_,
    ⟨b, ?_⟩⟩
  · rw [vsStreamLen, hlay, hra, ← stream_lengthC hok, e14]
    exact (readsAt_eq_streamAt hm.stream).symm
  · simp only [vsOpenArgs, e1171, e1172, e1627, e419, e434, e726]
    rfl
  · simp only [Prod.mk.injEq] at hrets
    simp only [vsOpenRets, hrets]

end Decode

/-! ## `verify_sub`, placed -/

variable {fs : String → ℕ} {cert : String → V → ℕ} {bytecode : List K} {D : VsData} {R : VsRunC}
  {CM : CompModel}

theorem vsSizes_leC (hok : D.OkC CM bytecode R) : (vsSizes D).sum ≤ 9086 := by
  have hd : D.gr.2.1.length < 33 := by rw [hok.point_length]; exact hok.depth_lt
  have hτ := tau_ltC hok
  simp only [vsSizes, List.sum_cons, List.sum_nil]
  omega

theorem vsKids1_boundC {fp lpA sqA outA : ℕ} (Bs : VsBounds) :
    kidsBound fs (vsBd fs Bs) (vsKids1C fs D R fp lpA sqA outA) ≤ vsKidsBound fs Bs := by
  simp (config := { decide := true }) only [kidsBound, vsKids1C, vsBd, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, ↓reduceIte, vsKidsBound]
  split <;> omega

theorem vsKids1_boundWC {fp lpA sqA outA : ℕ} {Θ : Type} (w : Θ → String → ℕ)
    (H : VsWeightHypsS CM.sem w) (Bsw : VsBoundsW Θ) (θ : Θ) :
    Main.kidsBoundW (vsBdWS w H Bsw) (vsKids1C fs D R fp lpA sqA outA) θ ≤
      vsKidsBoundWS w H Bsw θ := by
  simp (config := { decide := true }) only [Main.kidsBoundW, vsKids1C, vsBdWS, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, vsKidsBoundWS]
  split <;> omega

/-- **`verify_sub` is complete over the model**, uniformly and placed (`verify_sub_completeAtW`):
on a run record the model answers, the run within the deployed limits over the model, from its
callees' placed completeness over the model, by a node of `verify_sub` within its callees' weights
under `CM.sem` whose valuation decodes the run (`VsDecodes`). -/
theorem verify_sub_completeAtWC {κ : ℕ} (hκ : 7 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {Θ : Type} {w : Θ → String → ℕ} (H : VsWeightHypsS CM.sem w) {Bsw : VsBoundsW Θ}
    {Bs : VsBounds} (hG : CompleteGkrAtWC CM fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtWC CM fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtWC CM fs cert κ w Bs.fl Bsw.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl) (hO : CompleteOpenAtBC CM fs cert κ CapOk Bs.op)
    (hE : CompleteTermAtW fs cert κ TCtx PCtx w Bs.term Bsw.term)
    (hb : bytecode.length = 2 ^ 22) (hR : R.Ans CM D) (hok : D.OkC CM bytecode R)
    (htok : D.TOk bytecode)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root R.cvL D.xsW D.os
      (R.target D))
    (lpA sqA outA : ℕ) :
    CompleteAtWSRoot CM.sem fs cert w κ "verify_sub" (vsExtLC lpA sqA outA D R)
      [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
        (digestScalars D.seed).2, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA),
        ofK (Parameters.gpow outA)] (Returns []) (vsBound fs Bs) (fun θ => vsBoundWS w H Bsw θ)
      fun fp rd σ => VsDecodes bytecode D R fs fp rd σ := by
  intro fp
  have hfit := vsBufs_fitC hok htok
  -- the calls before the dispatch
  obtain ⟨N1, L1, outs1, ho1, hw1, hd1, hb1, hi1, hK1⟩ :=
    Main.kidsFromInWS_of_kidsBW κ (vsBd fs Bs) (vsBdWS w H Bsw) (vsKids1C fs D R fp lpA sqA outA)
    (vsKids1_completeWC hb hok htok H hG hT hF hPl hκ)
    (fp + fs "verify_sub" + (vsSizes D).sum)
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, rfl⟩ :=
    list12 (ho1.length.trans (by simp [vsKids1C]))
  have h10 : PlaceOut D o10.1 o10.2 := by
    simp only [OutsOk, vsKids1C, forall_const] at ho1
    exact ho1.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨off, kap, hr10, hpc⟩ := h10
  -- the opening
  obtain ⟨N2, L2, outs2, ho2, hw2, hd2, hb2, hi2, hK2⟩ :=
    Main.kidsFromInWS_of_kidsBW κ (fun _ => Bs.op) (fun _ θ => H.os θ)
    [vsOpenKidC fs bytecode D R fp lpA sqA outA] (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk; exact vsOpenKid_completeWC H hok hO hcap)
    (fp + fs "verify_sub" + (vsSizes D).sum + N1)
  obtain ⟨oO, rfl⟩ := list1 (ho2.length.trans rfl)
  have hoO : OpenOutK D oO.1 oO.2 := by simpa [OutsOk, vsOpenKidC] using ho2
  obtain ⟨bp, hr2, hLo⟩ := hoO
  set ptw := D.w.point ++ List.replicate (pointCap - D.w.point.length) 0
  -- the terminal
  obtain ⟨N3, L3, outs3, ho3, hw3, hd3, hb3, hi3, hK3⟩ :=
    Main.kidsFromInWS_of_kidsBW κ (fun _ => Bs.term) (fun _ => Bsw.term)
    [vsTermKidC fs D R fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]]
    (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk; exact vsTermKid_completeWC hb hok htok hE hpc)
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
  have h := relAtInWS_of_walk_root (S := CM.sem) (fs := fs) (cert := cert) (w := w)
    (R := RegionL (vsExtLC lpA sqA outA D R)) (D := RegionL []) (Dk := fun _ => False)
    (N := N1 + (N2 + N3)) (fp := fp)
    (bws := Main.kidsWs (vsBdWS w H Bsw) (vsKids1C fs D R fp lpA sqA outA) ++
      (Main.kidsWs (fun _ θ => H.os θ) [vsOpenKidC fs bytecode D R fp lpA sqA outA] ++
        Main.kidsWs (fun _ => Bsw.term)
          [vsTermKidC fs D R fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]]))
    (Q := VsDecodes bytecode D R fs fp rd) hdec
    find_verify_sub (Or.inl vs_not_loop) hpar hw
    rfl (fun e he => (hev e he).1) (by rw [hal]; exact hbuf)
    (by rw [(vs_parts σ sel).2.2.1]; simp) ?_ ?_ (fun i ⟨q, hq, _⟩ => by simp at hq)
  · rw [hal] at h
    obtain ⟨σ', bufs, ks, hQ, hv, hbo, hp, htot, hl, hd, hwt⟩ := h
    refine ⟨σ', bufs, ks, hQ, hv, hbo, hp, htot, hl, hd, fun θ => (hwt θ).trans ?_⟩
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
    refine Main.kidsFromInWS_append _ _ _ _ _ _ _ _ _ _
      (by rw [Main.kidsWs_length]; exact (Main.callsMatch_length hm1).symm) (hK1 rd σ _ _ (fun _ => False)
      hm1 (hlow) hL1 (memL_lins ?_) (regionsOk_of ?_))
      fun Dacc' hD1 => Main.kidsFromInWS_append [_] [_] _ _ _ _ _ _ _ _ rfl (hK2 rd σ _ _ Dacc'
        (matchOpenC hTo hr2) hlow hL2
        (memL_lins ?_) (regionsOk_of ?_))
        fun Dacc'' hD2 => Main.kidsFromInWS_dend _ _ _ _ _ (fun _ h => h.elim) (hK3 rd σ _ _ Dacc''
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

/-- **`verify_sub` is complete over the model**, uniformly and placed (`verify_sub_completeAtW`),
the node forgotten. -/
theorem verify_sub_completeAtWSC {κ : ℕ} (hκ : 7 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {Θ : Type} {w : Θ → String → ℕ} (H : VsWeightHypsS CM.sem w) {Bsw : VsBoundsW Θ}
    {Bs : VsBounds} (hG : CompleteGkrAtWC CM fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtWC CM fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtWC CM fs cert κ w Bs.fl Bsw.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl) (hO : CompleteOpenAtBC CM fs cert κ CapOk Bs.op)
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
  (verify_sub_completeAtWC hκ H hG hT hF hPl hO hE hb hR hok htok hcap lpA sqA outA).toWS

/-! ## At the deployed model -/

/-- **The deployed `verify_sub` placed, its node decoding the run**: `verify_sub_completeAtWC` at
`CompModel.deployed` on the deployed run (`VsRunC.ofD`). -/
theorem verify_sub_completeAtWRoot_of_comp {κ : ℕ} (hκ : 7 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {Θ : Type} {w : Θ → String → ℕ} (H : VsWeightHyps w) {Bsw : VsBoundsW Θ}
    {Bs : VsBounds} (hG : CompleteGkrAtW fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtW fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtW fs cert κ w Bs.fl Bsw.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl) (hO : CompleteOpenAtB fs cert κ CapOk Bs.op)
    (hE : CompleteTermAtW fs cert κ TCtx PCtx w Bs.term Bsw.term)
    (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (htok : D.TOk bytecode)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os
      D.target)
    (lpA sqA outA : ℕ) :
    CompleteAtWSRoot blakeDeployed fs cert w κ "verify_sub" (vsExtL lpA sqA outA D)
      [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
        (digestScalars D.seed).2, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA),
        ofK (Parameters.gpow outA)] (Returns []) (vsBound fs Bs) (fun θ => vsBoundW w H Bsw θ)
      fun fp rd σ => VsDecodes bytecode D (VsRunC.ofD D) fs fp rd σ := by
  have h := verify_sub_completeAtWC (CM := CompModel.deployed) hκ H.toS hG.toC hT.toC hF.toC hPl
    hO.toC hE hb (VsRunC.ans_ofD D) hok.toOkC htok
    (by rw [VsRunC.cvL_ofD, VsRunC.target_ofD]; exact hcap) lpA sqA outA
  rw [vsExtLC_ofD] at h
  exact h

/-- **The deployed `verify_sub_completeAtW`**, from the model's at `CompModel.deployed`. -/
theorem verify_sub_completeAtW_of_comp {κ : ℕ} (hκ : 7 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {Θ : Type} {w : Θ → String → ℕ} (H : VsWeightHyps w) {Bsw : VsBoundsW Θ}
    {Bs : VsBounds} (hG : CompleteGkrAtW fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtW fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtW fs cert κ w Bs.fl Bsw.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl) (hO : CompleteOpenAtB fs cert κ CapOk Bs.op)
    (hE : CompleteTermAtW fs cert κ TCtx PCtx w Bs.term Bsw.term)
    (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (htok : D.TOk bytecode)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os
      D.target)
    (lpA sqA outA : ℕ) :
    Main.CompleteAtW fs cert w κ "verify_sub" (vsExtL lpA sqA outA D)
      [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
        (digestScalars D.seed).2, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA),
        ofK (Parameters.gpow outA)] (Returns []) (vsBound fs Bs) fun θ => vsBoundW w H Bsw θ :=
  completeAtWS_deployed.mp
    (verify_sub_completeAtWRoot_of_comp hκ H hG hT hF hPl hO hE hb hok htok hcap lpA sqA outA).toWS

end
end LeanVM.Guest.B1.VerifySub
