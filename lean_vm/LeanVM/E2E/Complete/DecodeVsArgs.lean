/-
  LeanVM.E2E.Complete.DecodeVsArgs

  The words of child `c`'s `verify_sub` call as V_I's decoder reads them off the honest memory are
  the call's words in the honest tree.
-/

module

public import LeanVM.E2E.Complete.DecodeImage
public import LeanVM.E2E.Complete.DecodeMain
public import LeanVM.E2E.Complete.DecodeInsts

/-!
# The children's `verify_sub` words, decoded

V_I's decoder reads child `c`'s `verify_sub` call words (`vsArgsAt L c`) off `main`'s frame: the
child's public input digest's cells at `cpi·g^(2c)` (`main`'s value `123`), the seed's cells
(`63`, `64`), the exponent tables (`65`, `66`), and the fresh claims' slot `cfresh·g^(106c)`
(`133`). In the honest tree, the `__loop5` iteration `c` calls `verify_sub` on its values
`65, 66, 13, 14, 16, 6, 79`: the digest's cells it loaded from `cpi·g^(2c)` (values `68`, `69`),
the seed and the tables it was handed, and `cfresh·g^(106c)`. Hence (`vsArgsAt_honest`) the
decoded words are the call's, on the honest memory:

* `mainNamedUses`, `mainFrame_eqN`: `main`'s frame reads its root valuation at every value its
  straight-line prologue and middle name (`mainFrame_eq` beyond the prologue);
* `loadEqns_sub_insts`: an instance's load equations are its tree's;
* `loop5_load_eqns`: the iteration's two digest loads are load equations of its node;
* `loop5ValC_*`, `mainVal_*`: the honest words of the iteration and of `main`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (mainPre mainMid mainEvs walk_mainBody mainBody cellAt)
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-! ## `main`'s frame beyond its prologue -/

/-- The values a straight-line statement names, whatever the valuation. -/
def slUses : Stmt → List V
  | .atom a => atomUses a
  | .call _ args rets => args ++ rets
  | .callIf c _ args => c :: args
  | _ => []

theorem slUses_sub (σ : Val) : ∀ (s : Stmt) {v : V}, v ∈ slUses s →
    v ∈ (slEvs σ s).flatMap Memory.Ev.uses
  | .atom a, v, h => by simpa [slEvs, slUses, Memory.Ev.uses] using h
  | .call f args rets, v, h => by simpa [slEvs, slUses, Memory.Ev.uses] using h
  | .callIf c f args, v, h => by
      simp only [slUses, List.mem_cons] at h
      by_cases hc : σ c = 0 <;> simp [slEvs, Memory.Ev.uses, hc, h]
  | .ite .., v, h | .match_ .., v, h | .dispatch .., v, h | .ret _, v, h => by
      simp [slUses] at h

/-- The values `main`'s prologue and middle name. -/
def mainNamedUses : List V := (mainPre ++ mainMid).flatMap slUses

theorem mem_mainEvs_named {σ : Val} {v : V} (hv : v ∈ mainNamedUses) :
    v ∈ (mainEvs σ).flatMap Memory.Ev.uses := by
  obtain ⟨s, hs, hv⟩ := List.mem_flatMap.mp hv
  have hu := slUses_sub σ s hv
  obtain ⟨e, he, hve⟩ := List.mem_flatMap.mp hu
  refine List.mem_flatMap.mpr ⟨e, ?_, hve⟩
  rw [mainEvs]
  rcases List.mem_append.mp hs with hs | hs
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, he⟩)
  · refine List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, he⟩))))

/-- **`main`'s frame reads its root valuation** at every value its prologue and middle name, its
cell in the frame (`mainFrame_eq`). -/
theorem mainFrame_eqN {S : BlakeSem} (hB : B2C.B2HypsB S) {hdr : E × E} {rd : Reader} {T : Memory.Tree}
    (hname : T.name = "main")
    (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])
    {σ : Val} {bufs : List ℕ} {ks : List Memory.Tree} (hT : T = .node "main" σ bufs ks) {v : V}
    (hv : v ∈ mainNamedUses) (h2 : 2 ≤ cellJ 1 v) (hn : cellJ 1 v < fsN 1) :
    mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr T) v = σ v := by
  obtain ⟨I, hI, hIt, hfp, -⟩ := root_inst (P := coreProgram) (fs := B2C.fs) (H := B2C.H) (hdr := hdr)
    (T := T)
  have hw : walk σ (coreOf 1).body = .ret (mainEvs σ) [] := by
    rw [coreOf_one_body]; exact walk_mainBody σ
  have hF := hB.frame hdr rd T hname hH I hI "main" σ bufs ks (by rw [hIt, hT]) 1 B2C.idxOf_main
    (mainEvs σ) [] hw
  have := hF.val v (by
    simp only [B2C.namedOf, List.mem_append]
    exact Or.inl (Or.inr (mem_mainEvs_named hv))) h2 hn
  rw [hfp, Nat.zero_add] at this
  show (Check.wd (honest coreProgram B2C.fs B2C.H B2C.C hdr T) 1 ((certOf 1).locs.getD v.idx 0)) = σ v
  unfold Check.wd
  rw [one_mul]
  show ((honest coreProgram B2C.fs B2C.H B2C.C hdr T).read (Parameters.gpow (cellJ 1 v))).getD 0 = σ v
  rw [this]
  rfl

/-! ## Instances' load equations -/

section Insts

variable {P : Core.Program} {fs : String → ℕ} {lp : String → Bool} {H : Inst → ℕ → E × E}

mutual
/-- **An instance's load equations are its tree's.** -/
theorem loadEqns_sub_insts : ∀ (t : Memory.Tree) (fp : ℕ) (hdr : E × E), ∀ I ∈ t.insts fs lp H fp hdr,
    ∀ q ∈ I.t.loadEqns P, q ∈ t.loadEqns P
  | .node f σ bufs kids, fp, hdr, I, hI, q, hq => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact hq
      · rw [Memory.Tree.loadEqns, List.mem_append]
        exact Or.inr (loadEqnsKids_sub_insts kids _ _ 0 I hI q hq)
  | .phantom f σ, fp, hdr, I, hI, q, hq => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      exact hq

/-- `loadEqns_sub_insts` for the callees. -/
theorem loadEqnsKids_sub_insts : ∀ (ks : List Memory.Tree) (ps : List ℕ) (I : Inst) (j : ℕ),
    ∀ J ∈ Memory.Tree.instsKids fs lp H I j ps ks, ∀ q ∈ J.t.loadEqns P, q ∈ Memory.Tree.loadEqnsKids P ks
  | [], _, _, _, J, hJ, _, _ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, J, hJ, _, _ => by
      rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, p :: ps, I, j, J, hJ, q, hq => by
      rw [instsKids_cons, List.mem_append] at hJ
      rw [Memory.Tree.loadEqnsKids, List.mem_append]
      rcases hJ with hJ | hJ
      · exact Or.inl (loadEqns_sub_insts k _ _ J hJ q hq)
      · exact Or.inr (loadEqnsKids_sub_insts ks ps I (j + 1) J hJ q hq)
end

end Insts

/-- **The honest memory reads every honest instance's load equations.** -/
theorem honest_read_inst {S : BlakeSem} {hdr : E × E} {T : Memory.Tree} {rd : Reader} {args rets : List E}
    (hH : HonestB S coreProgram B2C.fs B2C.H B2C.C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T) :
    ∀ q ∈ I.t.loadEqns coreProgram, (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read q.1 = some q.2 :=
  fun q hq => hH.read_eqn (mem_eqns_of_mem_loadEqns _ (loadEqns_sub_insts T 0 hdr I hI q hq))

/-! ## The iteration's loads -/

/-- The loads of a block of statements: destination, pointer, offset. -/
def loadsOf : List Stmt → List (V × V × ℕ)
  | [] => []
  | .atom (.load d p o) :: ss => (d, p, o) :: loadsOf ss
  | _ :: ss => loadsOf ss

theorem mem_of_loadsOf : ∀ {ss : List Stmt} {d p : V} {o : ℕ}, (d, p, o) ∈ loadsOf ss →
    Stmt.atom (.load d p o) ∈ ss
  | [], _, _, _, h => by simp [loadsOf] at h
  | s :: ss, d, p, o, h => by
      match s with
      | .atom (.load d' p' o') =>
          simp only [loadsOf, List.mem_cons, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩ | h
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (mem_of_loadsOf h)
      | .atom (.const ..) | .atom (.add ..) | .atom (.mul ..) | .atom (.copy ..)
      | .atom (.assertEq ..) | .atom (.assertNe ..) | .atom (.rangeCheck ..) | .atom (.assertInK ..)
      | .atom (.blake2s ..) | .atom (.frameAddr ..) | .atom (.hint _) | .ite .. | .match_ ..
      | .call .. | .callIf .. | .dispatch .. | .ret _ =>
          exact List.mem_cons_of_mem _ (mem_of_loadsOf (by simpa [loadsOf] using h))

set_option maxRecDepth 100000 in
theorem loop5_digest_loads : (.n 65, .n 68, 0) ∈ loadsOf B1.Main.loop5Pre ∧
    (.n 66, .n 69, 1) ∈ loadsOf B1.Main.loop5Pre := by
  constructor <;> decide +kernel

/-- **The iteration's digest loads are load equations of its node.** -/
theorem loop5_load_eqns {σ : Val} {bufs : List ℕ} {ks : List Memory.Tree} :
    ((σ (.n 68)).limb 0 * Parameters.gpow 0, σ (.n 65)) ∈ (Memory.Tree.node "__loop5" σ bufs ks).loadEqns coreProgram ∧
      ((σ (.n 69)).limb 0 * Parameters.gpow 1, σ (.n 66)) ∈
        (Memory.Tree.node "__loop5" σ bufs ks).loadEqns coreProgram := by
  have hw : walk σ (Fn.body Data.core35) = .ret (B1.Main.loop5Pre.flatMap (slEvs σ)) [] := by
    rw [B1.Main.core35_split]
    exact walk_straight σ [] _ B1.Main.loop5_parts.1
  have hev := events_node (P := coreProgram) (bufs := bufs) (kids := ks) B1.Main.find_loop5 hw
  have hl : ∀ {d p : V} {o : ℕ}, (d, p, o) ∈ loadsOf B1.Main.loop5Pre →
      ((σ p).limb 0 * Parameters.gpow o, σ d) ∈ (Memory.Tree.node "__loop5" σ bufs ks).loadEqns coreProgram := by
    intro d p o h
    rw [Memory.Tree.loadEqns, hev]
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨.atom (.load d p o), ?_, ?_⟩)
    · exact List.mem_flatMap.mpr ⟨_, mem_of_loadsOf h, by simp [slEvs]⟩
    · simp [atomLoadEqns]
  exact ⟨hl loop5_digest_loads.1, hl loop5_digest_loads.2⟩

/-! ## The honest words -/

/-- `main`'s honest words at the values the decoder reads for the children's calls. -/
theorem mainVal_vsWords (fs : String → ℕ) (rd : Reader) (fp : ℕ) (W : B1.Main.MainWords) :
    [63, 64, 65, 66, 123, 133].map (fun i => B1.Main.mainVal rd (B1.Main.mainRunAt fs fp W) (.n i)) =
      [(digestScalars W.seed).1, (digestScalars W.seed).2, ofK (Parameters.gpow (B1.Main.mainExpBase fs fp W)),
        ofK (Parameters.gpow (B1.Main.mainExpBase fs fp W + 34)), B1.Main.mainPtr fs fp W 5,
        B1.Main.mainPtr fs fp W 6] := by
  simp only [List.map_cons, List.map_nil, B1.Main.mainVal, B1.Main.mainRunAt]
  b1_look

/-- The iteration's honest words at its `verify_sub` call and digest loads. -/
theorem loop5ValC_vsWords (rd : Reader) (N written lxT cover lxS gsq spT spS carried daR daC daS
    seed0 seed1 cpi glp cfresh : E) (c : ℕ) (r : B1.Main.ChildWords) (sigp cda : E) (dd : Digest) :
    [13, 14, 16, 6, 79, 68, 69].map (fun i => B1.Main.loop5ValC rd N written lxT cover lxS gsq spT
      spS carried daR daC daS seed0 seed1 cpi glp cfresh c r sigp cda dd (.n i)) =
      [seed0, seed1, glp, gsq, cfresh * gen ^ (106 * c), cpi * gen ^ (2 * c), cpi * gen ^ (2 * c)] := by
  simp only [List.map_cons, List.map_nil, B1.Main.loop5ValC]
  b1_look

theorem mainFrame_vsWords_mem : [V.n 63, .n 64, .n 65, .n 66, .n 123, .n 133].all
    (fun v => decide (v ∈ mainNamedUses) && Nat.ble 2 (cellJ 1 v) && Nat.blt (cellJ 1 v) (fsN 1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem loop5_vsWords_uses : [V.n 65, .n 66, .n 13, .n 14, .n 16, .n 6, .n 79].all
    (fun v => decide (v ∈ Stmt.usesList (Fn.body Data.core35))) = true := by
  decide +kernel

/-! ## The decoded words -/

/-- **Child `c`'s `verify_sub` words, decoded, are the honest call's**: on the honest memory of
`main`'s re-chosen tree `T0` at `main`'s honest valuation, for an instance `I` of the re-chosen
`__loop5` iteration whose valuation is child `c`'s (`mainIQ`), the decoder's words are the
iteration's `verify_sub` call's. -/
theorem vsArgsAt_honest {S : BlakeSem} (hB : B2C.B2HypsB S) {hdr : E × E} {rd rd0 : Reader}
    {T0 : Memory.Tree} {ν : ℕ → String → Val → V → E} {σ0 : Val} {bufs : List ℕ} {ks : List Memory.Tree}
    (hT0 : T0 = .node "main" σ0 bufs ks)
    (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0) B2C.cert
      rd [] [])
    {W : B1.Main.MainWords} (hσ0 : σ0 = B1.Main.mainVal rd0 (B1.Main.mainRunAt B2C.fs 0 W))
    {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr (T0.retemp coreProgram B2C.fs ν 0))
    {σ : Val} {bufsI : List ℕ} {ksI : List Memory.Tree}
    (hIt : I.t = (Memory.Tree.node "__loop5" σ bufsI ksI).retemp coreProgram B2C.fs ν I.fp)
    {c : ℕ} {rd' : Reader} (hIQ : B1.Main.mainIQ B2C.fs 0 W c rd' σ) :
    vsArgsAt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) c =
      [V.n 65, .n 66, .n 13, .n 14, .n 16, .n 6, .n 79].map
        (retempVal coreProgram ν I.fp "__loop5" σ) := by
  set T := T0.retemp coreProgram B2C.fs ν 0 with hT
  set L := honest coreProgram B2C.fs B2C.H B2C.C hdr T with hL
  have hTn : T = .node "main" (retempVal coreProgram ν 0 "main" σ0) bufs
      (Memory.Tree.retempKids coreProgram B2C.fs ν (kidPos B2C.fs coreProgram.loop 0 "main" bufs
        (ks.map (Memory.Tree.total B2C.fs))) ks) := by
    rw [hT, hT0, retemp_node]
  have hname : T.name = "main" := by rw [hTn]; rfl
  -- `main`'s frame
  have hmf : ∀ i ∈ [63, 64, 65, 66, 123, 133], mainFrame L (.n i) =
      B1.Main.mainVal rd0 (B1.Main.mainRunAt B2C.fs 0 W) (.n i) := by
    intro i hi
    have hm := mainFrame_vsWords_mem
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
      Nat.ble_eq, Nat.blt_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    have key : ∀ v : V, v ∈ mainNamedUses → 2 ≤ cellJ 1 v → cellJ 1 v < fsN 1 →
        v ∈ Stmt.usesList (Fn.body Data.core0) →
        mainFrame L v = B1.Main.mainVal rd0 (B1.Main.mainRunAt B2C.fs 0 W) v := by
      intro v hv h2 hn hu
      rw [mainFrame_eqN hB hname hH hTn hv h2 hn,
        retempVal_uses coreProgram_fresh B1.Main.find_main hu, hσ0]
    have hus : [V.n 63, .n 64, .n 65, .n 66, .n 123, .n 133].all
        (fun v => decide (v ∈ Stmt.usesList (Fn.body Data.core0))) = true := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hus
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact key _ hm.1.1.1 hm.1.1.2 hm.1.2 hus.1
    · exact key _ hm.2.1.1.1 hm.2.1.1.2 hm.2.1.2 hus.2.1
    · exact key _ hm.2.2.1.1.1 hm.2.2.1.1.2 hm.2.2.1.2 hus.2.2.1
    · exact key _ hm.2.2.2.1.1.1 hm.2.2.2.1.1.2 hm.2.2.2.1.2 hus.2.2.2.1
    · exact key _ hm.2.2.2.2.1.1.1 hm.2.2.2.2.1.1.2 hm.2.2.2.2.1.2 hus.2.2.2.2.1
    · exact key _ hm.2.2.2.2.2.1.1 hm.2.2.2.2.2.1.2 hm.2.2.2.2.2.2 hus.2.2.2.2.2
  have hmv := mainVal_vsWords B2C.fs rd0 0 W
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmv
  obtain ⟨m63, m64, m65, m66, m123, m133, -⟩ := hmv
  -- the iteration's words
  obtain ⟨b, dd, rfl⟩ := hIQ
  have hlv := loop5ValC_vsWords rd' (gen ^ W.nc) (ofK (Parameters.gpow (B1.Main.mainBase B2C.fs 0 W 8)))
    (B1.Main.mainPtr B2C.fs 0 W 1) (B1.Main.mainPtr B2C.fs 0 W 4) (gen ^ W.dx * gen ^ W.ux)
    (ofK (Parameters.gpow (B1.Main.mainExpBase B2C.fs 0 W + 34))) (B1.Main.mainPtr B2C.fs 0 W 2)
    (gen ^ W.ds * gen ^ W.us) (B1.Main.mainPtr B2C.fs 0 W 7) (B1.Main.mainPtr B2C.fs 0 W 0)
    (B1.Main.mainPtr B2C.fs 0 W 4 * (gen ^ W.dx * gen ^ W.ux * (gen ^ W.ds * gen ^ W.us)))
    (gen ^ W.da * gen ^ W.ud) (digestScalars W.seed).1 (digestScalars W.seed).2
    (ofK (Parameters.gpow (B1.Main.mainBase B2C.fs 0 W 5))) (ofK (Parameters.gpow (B1.Main.mainExpBase B2C.fs 0 W)))
    (B1.Main.mainPtr B2C.fs 0 W 6) c (W.child c) (ofK (Parameters.gpow b)) (ofK (Parameters.gpow (b + 2))) dd
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hlv
  obtain ⟨l13, l14, l16, l6, l79, l68, l69, -⟩ := hlv
  set σc := B1.Main.loop5ValC rd' (gen ^ W.nc) (ofK (Parameters.gpow (B1.Main.mainBase B2C.fs 0 W 8)))
    (B1.Main.mainPtr B2C.fs 0 W 1) (B1.Main.mainPtr B2C.fs 0 W 4) (gen ^ W.dx * gen ^ W.ux)
    (ofK (Parameters.gpow (B1.Main.mainExpBase B2C.fs 0 W + 34))) (B1.Main.mainPtr B2C.fs 0 W 2)
    (gen ^ W.ds * gen ^ W.us) (B1.Main.mainPtr B2C.fs 0 W 7) (B1.Main.mainPtr B2C.fs 0 W 0)
    (B1.Main.mainPtr B2C.fs 0 W 4 * (gen ^ W.dx * gen ^ W.ux * (gen ^ W.ds * gen ^ W.us)))
    (gen ^ W.da * gen ^ W.ud) (digestScalars W.seed).1 (digestScalars W.seed).2
    (ofK (Parameters.gpow (B1.Main.mainBase B2C.fs 0 W 5))) (ofK (Parameters.gpow (B1.Main.mainExpBase B2C.fs 0 W)))
    (B1.Main.mainPtr B2C.fs 0 W 6) c (W.child c) (ofK (Parameters.gpow b)) (ofK (Parameters.gpow (b + 2))) dd with hσc
  -- the retemped iteration keeps its uses
  have hus := loop5_vsWords_uses
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hus
  have hr : ∀ v ∈ Stmt.usesList (Fn.body Data.core35), retempVal coreProgram ν I.fp "__loop5" σc v = σc v :=
    fun v hv => retempVal_uses coreProgram_fresh B1.Main.find_loop5 hv
  -- the digest's cells, read back
  have hld := loop5_load_eqns (σ := σc) (bufs := bufsI) (ks := ksI)
  have hread : ∀ q ∈ (Memory.Tree.node "__loop5" σc bufsI ksI).loadEqns coreProgram, L.read q.1 = some q.2 := by
    intro q hq
    have hq' : q ∈ I.t.loadEqns coreProgram := by
      rw [hIt, loadEqns_retemp coreProgram_fresh]; exact hq
    exact honest_read_inst hH.toHonestB hI q hq'
  have r65 := hread _ hld.1
  have r66 := hread _ hld.2
  have hcpi : ∀ k : ℕ, (σc (.n 68)).limb 0 * Parameters.gpow k =
      (B1.Main.mainPtr B2C.fs 0 W 5).limb 0 * Parameters.gpow (2 * c + k) := by
    intro k
    rw [l68, B1.Main.ofK_gpow_mul_gen, B1.Main.mainPtr, Check.limb_ofK0, Check.limb_ofK0,
      Parameters.gpow, Parameters.gpow, Parameters.gpow, Parameters.gpow, ← pow_add, ← pow_add,
      Nat.add_assoc]
  have hcpi' : ∀ k : ℕ, (σc (.n 69)).limb 0 * Parameters.gpow k =
      (B1.Main.mainPtr B2C.fs 0 W 5).limb 0 * Parameters.gpow (2 * c + k) := by
    intro k; rw [show σc (.n 69) = σc (.n 68) by rw [l68, l69]]; exact hcpi k
  rw [hcpi 0, Nat.add_zero] at r65
  rw [hcpi' 1] at r66
  unfold vsArgsAt
  rw [hmf 63 (by simp), hmf 64 (by simp), hmf 65 (by simp), hmf 66 (by simp), hmf 123 (by simp),
    hmf 133 (by simp), m63, m64, m65, m66, m123, m133]
  simp only [List.map_cons, List.map_nil, hr _ hus.1, hr _ hus.2.1, hr _ hus.2.2.1,
    hr _ hus.2.2.2.1, hr _ hus.2.2.2.2.1, hr _ hus.2.2.2.2.2.1, hr _ hus.2.2.2.2.2.2, l13, l14, l16,
    l6, l79, cellAt, r65, r66, Option.getD_some]
