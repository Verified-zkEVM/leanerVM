/-
  LeanVM.Guest.B1.Comp.VerifySub.PlacedEq

  `verify_sub` placed over a completeness model, its tree decoding the child proof on any reader
  satisfying the tree's memory equations.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.PlacedEqKids

/-!
# `verify_sub`'s child proof, decoded on the tree's equations

The image V_I decodes holds the frame cells and the tree's memory equations (`Tree.eqns`), not
every word of `verify_sub`'s buffers. Here what `verify_sub`'s tree decodes is stated on ANY reader
satisfying its equations:

* `VsFrame`: what the node's valuation `σ` alone gives (the public input and seed of its argument
  cells, the announced layout and rate, the dispatched opening's call words);
* `VsRootTreeE`: the tree is the node of `verify_sub` at `σ` with `VsFrame σ`; on every reader
  `rd'` satisfying the tree's equations the child proof's stream `streamAt rd' (σ 14)
  (vsStreamLen bytecode σ)` is `D.stream` (its first ten words loaded by `verify_sub` itself
  (`vs_own_loads`), the rest by GKR, the tables, Flock and the opening, `LoadsWords`); and one of its
  callees' trees, placed at some `b`, valid on every such `rd'` on the opening's call words,
  satisfies `OsQ … D.os b` (the Whir side's reader-free decoding of the openings);
* `verify_sub_completeAtWCE`: `verify_sub` placed over the model by such a tree;
* `vsProofOf_eq_proofE`: on every reader satisfying the tree's equations, an opening decoder
  reading `D.os` on the opening's call gives `vsProofOf bytecode rd' σ wO = D.proof`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## What the valuation alone decodes -/

/-- **What `verify_sub`'s valuation alone decodes** (`VsDecodes` without the stream): the public
input and seed, the announced layout and rate, the opening's call words. -/
structure VsFrame (bytecode : List K) (D : VsData) (R : VsRunC) (fs : String → ℕ) (fp : ℕ)
    (σ : Val) : Prop where
  pi : vsPiOf σ = D.pi
  seed : vsSeedOf σ = D.seed
  layout : vsLayout bytecode σ = layoutOf bytecode D.logMem D.rows
  rate : vsRate σ = D.rate
  openArgs : vsOpenArgs σ = [(digestScalars R.cvL).1, (digestScalars R.cvL).2, R.target D, D.x0,
    D.x1, curW D (vsPtrsAt fs fp D 0 0 0)]
  openRets : ∃ b, vsOpenRets σ = [D.w.target, ofK (Parameters.gpow b), D.w.inner, D.w.residual]

theorem VsDecodes.toFrame {bytecode : List K} {D : VsData} {R : VsRunC} {fs : String → ℕ} {fp : ℕ}
    {rd : Reader} {σ : Val} (h : VsDecodes bytecode D R fs fp rd σ) : VsFrame bytecode D R fs fp σ :=
  ⟨h.pi, h.seed, h.layout, h.rate, h.openArgs, h.openRets⟩

/-- **`verify_sub`'s tree decodes the run on its equations**: the node of `verify_sub` at `σ`
(`VsFrame`), the child proof's stream `D.stream` on every reader satisfying the tree's equations,
and the opening's tree, placed at `b`, valid there on the opening's call words, satisfying
`OsQ … D.os b`. -/
def VsRootTreeE (S : BlakeSem) (OsQ : ℕ → ℕ → List Opening → ℕ → Tree → Prop)
    (bytecode : List K) (D : VsData) (R : VsRunC) (fs : String → ℕ) (cert : String → V → ℕ)
    (fp : ℕ) (t : Tree) : Prop :=
  ∃ (σ : Val) (bufs : List ℕ) (ks : List Tree), t = Memory.Tree.node "verify_sub" σ bufs ks ∧
    VsFrame bytecode D R fs fp σ ∧
    (∀ rd' : Reader, (∀ q ∈ t.eqns coreProgram, rd' q.1 = some q.2) →
      streamAt rd' (σ (.n 14)) (vsStreamLen bytecode σ) = D.stream) ∧
    ∃ ko ∈ ks, ∃ b : ℕ, OsQ (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.os b ko ∧
      ko.Placed coreProgram fs cert b ∧
      ∀ rd' : Reader, (∀ q ∈ t.eqns coreProgram, rd' q.1 = some q.2) →
        ko.ValidB S coreProgram rd' (vsOpenArgs σ) (vsOpenRets σ)

/-- **The child proof on the tree's equations**: on any reader satisfying the equations of
`verify_sub`'s tree, an opening decoder reading the run's openings on the opening's call decodes
the run's proof. -/
theorem vsProofOf_eq_proofE {S : BlakeSem} {OsQ : ℕ → ℕ → List Opening → ℕ → Tree → Prop}
    {bytecode : List K} {D : VsData} {R : VsRunC} {fs : String → ℕ} {cert : String → V → ℕ}
    {fp : ℕ} {σ : Val} {bufs : List ℕ} {ks : List Tree}
    (h : VsRootTreeE S OsQ bytecode D R fs cert fp (Memory.Tree.node "verify_sub" σ bufs ks))
    (rd' : Reader) (he : ∀ q ∈ (Memory.Tree.node "verify_sub" σ bufs ks).eqns coreProgram,
      rd' q.1 = some q.2)
    (wO : String → List E → List E → List Opening)
    (hO : wO (openName (vsLayout bytecode σ).stackLog (vsRate σ)) (vsOpenArgs σ) (vsOpenRets σ) = D.os) :
    vsProofOf bytecode rd' σ wO = D.proof := by
  obtain ⟨σ', bufs', ks', ht, -, hs, -⟩ := h
  simp only [Memory.Tree.node.injEq] at ht
  obtain ⟨-, rfl, rfl, rfl⟩ := ht
  simp only [vsProofOf, hs rd' he, VsData.proof, hO]

/-! ## The words `verify_sub` loads itself -/

/-- The variable the `k`-th of the first ten stream words is loaded into. -/
def ownD (k : ℕ) : ℕ := if k < 8 then rdB k else if k = 8 then 419 else 434

/-- The body's statement loading it. -/
def ownI (k : ℕ) : ℕ := if k < 8 then rdN k else if k = 8 then 508 else 521

set_option maxRecDepth 100000 in
theorem vs_own_loads : ∀ k < 10, stmtsEqb [.atom (.load (.n (ownD k)) (.n 14) k)]
    ((vsPre.drop (ownI k)).take 1) = true := by decide +kernel

theorem ownI_lt : ∀ k < 10, ownI k < 1926 := by decide

/-- An atom of the body before the dispatch is an event of the path. -/
theorem mem_vsEvs_of {a : Atom} {i : ℕ} (h : stmtsEqb [.atom a] ((vsPre.drop i).take 1) = true)
    (hi : i < 1926) (σ : Val) (sel : ℕ) : Memory.Ev.atom a ∈ vsEvs σ sel := by
  have h1 := stmtsEqb_sound h
  have hmem : Stmt.atom a ∈ vsPre1 := by
    have h2 : Stmt.atom a ∈ (vsPre.drop i).take 1 := by rw [← h1]; exact List.mem_singleton_self _
    have h3 : (vsPre.drop i).take 1 = ((vsPre.take 1926).drop i).take 1 := by
      rw [List.drop_take, List.take_take]
      congr 1
      omega
    rw [h3] at h2
    have h4 := List.mem_of_mem_drop (List.mem_of_mem_take h2)
    unfold vsPre1
    rwa [← vsPre_eq]
  unfold vsEvs
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, hmem, by simp [Main.slEvs]⟩)

/-- **The first ten stream words are loaded by `verify_sub`'s own path**, at the stream buffer,
with the run's words. -/
theorem vs_own_words {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val} {sel : ℕ} {D : VsData}
    (hev : ∀ e ∈ vsEvs σ sel, e.OkB S C rd σ) (hs : ReadsAt rd (σ (.n 14)) D.stream)
    (hl : 10 ≤ D.stream.length) :
    ∀ k < 10, ((σ (.n 14)).limb 0 * Parameters.gpow k, D.stream.getD k 0) ∈
      evEqns σ (vsEvs σ sel) := by
  intro k hk
  have hm := mem_vsEvs_of (vs_own_loads k hk) (ownI_lt k hk) σ sel
  have hh := (hev _ hm).1
  simp only [Ev.HoldsB, Atom.HoldsB] at hh
  have hv : σ (.n (ownD k)) = D.stream.getD k 0 :=
    loadHolds_unique hh (readsAt_getD hs (by omega))
  rw [← hv]
  exact mem_evEqns hm (List.mem_singleton_self _)

/-! ## A callee's tree at a call -/

/-- **The tree `KidsSat` gives at the call `i`**, valid on its words. -/
theorem kidsSat_get {S : BlakeSem} {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Call} {qs : List (ℕ → Tree → Prop)} {bs : List ℕ} {ks : List Tree} (i : ℕ),
      Tree.KidsValidB S P rd σ cs ks → KidsSat cs qs bs ks → (hc : i < cs.length) →
      (hq : i < qs.length) → (hb : i < bs.length) → cs[i].taken = true →
      ∃ k ∈ ks, qs[i] bs[i] k ∧ k.ValidB S P rd (cs[i].args.map σ) (cs[i].rets.map σ)
  | c :: cs, q :: qs, b :: bs, k :: ks, 0, hv, hs, _, _, _, ht => by
    simp only [Tree.KidsValidB, KidsSat] at hv hs
    have ht' : c.taken = true := ht
    refine ⟨k, List.mem_cons_self, hs.1 ht', ?_⟩
    have := hv.2.1
    rw [ite_eq_left ht'] at this
    exact this
  | c :: cs, q :: qs, b :: bs, k :: ks, i + 1, hv, hs, hc, hq, hb, ht => by
    simp only [Tree.KidsValidB, KidsSat] at hv hs
    obtain ⟨k', hk', h1, h2⟩ := kidsSat_get i hv.2.2 hs.2 (by simpa using hc) (by simpa using hq)
      (by simpa using hb) (by simpa using ht)
    exact ⟨k', List.mem_cons_of_mem _ hk', by simpa using h1, by simpa using h2⟩
  | [], _, _, _, _, _, _, hc, _, _, _ => absurd hc (by simp)
  | _ :: _, [], _, _, _, _, _, _, hq, _, _ => absurd hq (by simp)
  | _ :: _, _ :: _, [], _, _, _, _, _, _, hb, _ => absurd hb (by simp)
  | _ :: _, _ :: _, _ :: _, [], _, hv, _, _, _, _, _ => by simp [Tree.KidsValidB] at hv

/-! ## The stream from the tree's loads -/

/-- **The stream on the tree's equations**: the first ten words at the stream buffer `g^s`, then
GKR's, the tables', Flock's and the opening's words. -/
theorem stream_wordsAt {D : VsData} {rd' : Reader} {s : ℕ} (hl : D.rows.length = 6)
    (h10 : ∀ k < 10, rd' (Parameters.gpow (s + k)) = some (D.stream.getD k 0))
    (hG : WordsAt rd' (s + 10) D.xsG) (hT : WordsAt rd' (s + 10 + D.xsG.length) D.xsT)
    (hF : WordsAt rd' (s + 10 + D.xsG.length + D.xsT.length) D.xsF)
    (hW : WordsAt rd' (s + 10 + D.xsG.length + D.xsT.length + D.xsF.length) D.xsW) :
    WordsAt rd' s D.stream := by
  have ha := ann_length hl
  have hst : D.stream = D.ann ++ D.x0 :: D.x1 :: (D.xsG ++ (D.xsT ++ (D.xsF ++ D.xsW))) := rfl
  have g : ∀ k (hk : k < D.stream.length), D.stream.getD k 0 = D.stream[k] := fun k hk =>
    List.getD_eq_getElem _ _ hk
  have hlen : 10 ≤ D.stream.length := by rw [hst]; simp [ha]; omega
  rw [hst]
  refine WordsAt.append (fun k hk => ?_) ?_
  · have := h10 k (by omega)
    rw [g k (by omega)] at this
    rw [this]
    congr 1
    simp only [hst, List.getElem_append_left hk]
  · rw [ha]
    refine WordsAt.cons ?_ (WordsAt.cons ?_ ?_)
    · have := h10 8 (by omega)
      rw [g 8 (by omega)] at this
      rw [this]; congr 1; simp [hst, List.getElem_append_right, ha]
    · have := h10 9 (by omega)
      rw [g 9 (by omega)] at this
      rw [show s + 8 + 1 = s + 9 by omega, this]; congr 1; simp [hst, List.getElem_append_right, ha]
    · refine WordsAt.append (hG.of_eq (by omega)) (WordsAt.append (hT.of_eq (by omega))
        (WordsAt.append (hF.of_eq (by omega)) (hW.of_eq (by simp))))

/-! ## `verify_sub`'s tree -/

theorem kidsValidB_length {S : BlakeSem} {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValidB S P rd σ cs ks → cs.length = ks.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [kidsValidB_length h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **`verify_sub`'s node decodes the run on its tree's equations**, from its path, its run
memory and its transcript callees' loads. -/
theorem vsRootTreeE_of {S : BlakeSem} {C : CallRel} {OsQ : ℕ → ℕ → List Opening → ℕ → Tree → Prop}
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
    (hv : ko.ValidB S coreProgram rd (vsOpenArgs σ) (vsOpenRets σ)) :
    VsRootTreeE S OsQ bytecode D R fs cert fp (Memory.Tree.node "verify_sub" σ bufs ks) := by
  have hE : (Memory.Tree.node "verify_sub" σ bufs ks).eqns coreProgram =
      evEqns σ (vsEvs σ sel) ++ Tree.eqnsKids coreProgram ks := eqns_node find_verify_sub hw
  have hkid : ∀ {k : Tree}, k ∈ ks → ∀ q ∈ k.eqns coreProgram,
      q ∈ (Memory.Tree.node "verify_sub" σ bufs ks).eqns coreProgram := fun hk q hq => by
    rw [hE]; exact List.mem_append_right _ (eqns_of_mem_kids hk q hq)
  have hlen : 10 ≤ D.stream.length := by
    simp [VsData.stream, ann_length hok.rows_length]; omega
  refine ⟨σ, bufs, ks, rfl, hdec.toFrame, fun rd' he => ?_, ko, hko, b, hq, hp, fun rd' he =>
    Tree.ValidB.transfer ko hv fun q hq => he q (hkid hko q hq)⟩
  have h10 : ∀ k < 10, rd' (Parameters.gpow (vsB fs fp D 2 + k)) = some (D.stream.getD k 0) := by
    intro k hk
    have := he _ (by rw [hE]; exact List.mem_append_left _ (vs_own_words hev hs hlen k hk))
    rwa [h14, Main.addr_ofK] at this
  have hw' := stream_wordsAt hok.rows_length h10
    (wordsAt_of_loads hG fun q hq => he q (hkid hkG q hq))
    (wordsAt_of_loads hT fun q hq => he q (hkid hkT q hq))
    (wordsAt_of_loads hF fun q hq => he q (hkid hkF q hq))
    (wordsAt_of_loads hW fun q hq => he q (hkid hko q hq))
  have hsl : vsStreamLen bytecode σ = D.stream.length := by
    rw [vsStreamLen, hdec.layout, hdec.rate, stream_lengthC hok]
  rw [h14, hsl]
  exact streamAt_of_wordsAt hw'

variable {fs : String → ℕ} {cert : String → V → ℕ} {bytecode : List K} {D : VsData} {R : VsRunC}
  {CM : CompModel}

/-- **`verify_sub` is complete over the model, its tree decoding the run on its equations**
(`verify_sub_completeAtWCT`): the transcript callees loading the words they read
(`CompleteGkrAtWCL`, `CompleteTablesAtWCL`, `CompleteFlockAtWCL`, `CompleteOpenAtBCL`). -/
theorem verify_sub_completeAtWCE {κ : ℕ} (hκ : 7 ≤ κ)
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
      fun fp _ t => VsRootTreeE CM.sem OsQ bytecode D R fs cert fp t := by
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
    (Q := VsRootTreeE CM.sem OsQ bytecode D R fs cert fp)
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
    obtain ⟨ko, hko, b, hq, hv, -⟩ := kidsSat_at (qs1 := (vsKids1C fs D R fp lpA sqA outA).map
      (fun k b t => VsKidsQ fs fp D k b rd t)) hkv (by simp [vsKids1C, vsPre1_calls]) (by simpa using hkq)
      (by simp [length_bases])
    have h14 : σ (.n 14) = ofK (Parameters.gpow (vsB fs fp D 2)) :=
      (hfix.get (k := 14) (e := (vsPtrsAt fs fp D off kap (ofK (Parameters.gpow bp))).stream)
        (by vs_memC)).trans rfl
    exact vsRootTreeE_of hok hw hev hdec h14 (by rw [h14]; exact hm0.stream) hkG (hqG.1 rfl) hkT
      (hqT.2.1 rfl) hkF (hqF.2.2 rfl) hko (hq rfl).1.1 (hq rfl).1.2 (hq rfl).2
      (by simpa [vsOpenArgs, vsOpenRets] using hv rfl)

end
end LeanVM.Guest.B1.VerifySub
