/-
  LeanVM.E2E.Complete.HonestBodiesPad

  The honest bodies at the honest frames (`HonestBodies.lean`, `HonestVs.lean`) on an extension of
  the honest memory, its zero padding: the guest's code holds there under the honest run's table.
-/

module

public import LeanVM.E2E.Complete.PadHonest
public import LeanVM.E2E.Complete.HonestVs

/-!
# The honest bodies on an extended memory

`honest_bodyAt`'s proof with the memory an extension `L'` of the honest memory (`MemExt`, its
zero padding, of `2^κ'` words, `16 ≤ κ' ≤ 32`): the run, the frames, the jump tables and the
precondition transport to `L'` (`PadHonest.lean`); B2's contracts hold on `L'` (`End.b2B_step`
holds on every memory of the admissible sizes); the run's rows on `L'` are its rows on the honest
memory (`blakeRows_of_ext`), so the table semantics is `honestSem`. Hence:

* `honest_bodyAt_ext`, `honest_bodyAt_plain_ext`: `BodyAtB (honestSem hdr T n) L' f args rets I.fp`
  at an honest node instance of a function `j ≠ 1`;
* `honest_vs_bodyAt_ext`: `verify_sub`'s body at its honest frame, the exponent tables handed down;
* `honest_main_bodyAt_ext`: `main`'s body at frame `0`;
* `honest_valAt_ext`: the decoder's valuation at an honest frame of `L'` is the instance's.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check LeanVM.Guest.Value
open LeanVM.Guest.End (mainEntry JumpTables)
open LeanVM.Guest.Exec (index EnvHolds envOf Sym)

@[expose] public section

section Honest

variable {S : BlakeSem} (hfun : B2C.SemFunctional S)
  (hcan : ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
    CanonicalCells m cv0 cv1 o0 o1 md)
  {hdr : E × E} {rd : Reader} {T : Tree} (hname : T.name = "main")
  (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])
  {n : ℕ} (hrun : runB S guest (honest coreProgram B2C.fs B2C.H B2C.C hdr T) n Regs.initial =
    some (Regs.final guest))
  {κ' : ℕ} {L' : MemImage κ'} (hX : MemExt (honest coreProgram B2C.fs B2C.H B2C.C hdr T) L')
  (h16' : minLogMem ≤ κ') (h32' : κ' ≤ maxLogMem)

include hcan hrun hX in
/-- **The run's table on the extension is the honest run's.** -/
theorem honestSem_ext :
    tableSem (Trace.blakeRows blakeFree (⟨κ', L', n⟩ : Trace guest)) = honestSem hdr T n := by
  rw [blakeRows_of_ext (S := S) (fun _ hc ↦ hcan hc) hX.read hrun]

include hrun hX in
/-- The halting run on the extension. -/
theorem honest_run_ext : runB S guest L' n Regs.initial = some (Regs.final guest) :=
  runB_of_ext hX.read n hrun

include hfun hcan hrun h16' h32' in
/-- **Every contract holds on the extension under the honest run's table.** -/
theorem honest_contracts_ext (j : ℕ) :
    FunSpecB (honestSem hdr T n) guest L' (glob.sig j).entry (Pre glob L' j)
      (PostB (honestSem hdr T n) coreProgram glob L' certByName j) :=
  funSpecB_induction (End.b2B_step (honest_vsKnown hfun hcan hrun) L' h16' h32') j

include hfun hcan hname hH hrun hX h16' h32' in
/-- **The honest body at an honest frame, on the extension** (`honest_bodyAt`). -/
theorem honest_bodyAt_ext {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {j : ℕ} (hj : B2C.idxOf f = some j) (hj1 : j ≠ 1)
    (hpre : BndHolds L' (gpow I.fp) (certOf j).pre ∧ MemPre L' (gpow I.fp) (certOf j).mem ∧
      SemHolds glob L' (gpow I.fp) (certOf j).sem)
    {args rets : List E}
    (hv : I.t.ValidB S coreProgram (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read args rets) :
    Located.BodyAtB (honestSem hdr T n) L' f args rets I.fp := by
  set L := honest coreProgram B2C.fs B2C.H B2C.C hdr T with hL
  have h := B2C.b2HypsB hfun
  obtain ⟨i, rfl, hi, hn', hfind, hcore, -, -, h1, hlt⟩ := B2C.fn_of_idx hj
  have hcn : (coreOf (i + 1)).name = f := by rw [hcore]; exact hn'
  -- on the run
  obtain ⟨-, hm, hon⟩ := B2C.honest_onRun h hname hH I hI f σ bufs kids ht
  obtain ⟨hon0, r, -, hon1, hon2⟩ := hX.onRunB hon
  have hjt : JumpTables L' := hX.jumpTables (B2C.jumpTablesB_honestC hH.toHonestB hname)
  have hpro : ReachB S guest L' Regs.initial ⟨gpow mainEntry, 1⟩ := by
    have := (B2C.runCB_jumpTables (S := S) hjt).reach
    rwa [show (⟨gpow 0, 1⟩ : Regs K) = Regs.initial by rw [gpow, pow_zero]; rfl] at this
  have hent : B2C.entryOf I.t.name = (fnOf (i + 1)).entry := by rw [ht]; exact B2C.entryOf_of hj
  obtain ⟨a, ha⟩ := hpro.trans hon0
  obtain ⟨b, hb⟩ := hon1.trans hon2
  rw [hent] at ha hb
  have hsafe : SafeB (honestSem hdr T n) guest L' b ⟨gpow (fnOf (i + 1)).entry, gpow I.fp⟩ := by
    have h0 := safe_tableSem_of_segment (fun _ hc ↦ hcan hc) (honest_run_ext hrun hX) ha hb
    have e : tableSem (runRows blakeFree guest L' n Regs.initial) = honestSem hdr T n :=
      honestSem_ext hcan hrun hX
    rw [e] at h0
    exact h0
  -- the frame
  have hH' := hH.toHonestB
  obtain ⟨es, vs, hw, hev, -⟩ := B2C.nodeB_valid ht hj (instsB_good T 0 hdr hH'.valid I hI)
  have hF := hX.frameHolds (h.frame hdr rd T hname hH I hI f σ bufs kids ht (i + 1) hj es vs hw)
  have hc0 := B2C.Cplw.cplOk_all (i + 1) h1 hlt 0 (Nat.zero_le _) 0 (B2C.one_le_nParts (i + 1) 0)
  have hw0 := B2C.winOkC_of hc0
  simp only [B2C.winOkC, Bool.and_eq_true, Nat.beq_refl, Bool.cond_true] at hw0
  have henv := hw0.2.2
  have hX' := B2C.cxOk hF (End.certOf_pows_ok (i + 1)) (index (B2C.segsW (i + 1) 0))
    (B2C.clocW (certOf (i + 1)) 0) (B2C.nvOf (B2C.partStmts (i + 1) 0 0) 0) none
  have hE : EnvHolds L' (gpow I.fp) (envOf (certOf (i + 1)).facts.env) := by
    refine envOf_holds fun p hp ↦ ?_
    have := List.all_eq_true.mp henv p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨h1', h2'⟩ := this
    have := hX'.stat p.1 _ h2'
    rw [Sym.beq_eq h1']
    simp only [B2C.PC.word, Nat.add_zero] at this
    simpa [Sym.val, B2C.gpow_addC] using this
  -- B2's soundness at the frame
  have hc := End.winOk_of h1 hlt
  have h1' : ((i + 1) == 1) = false := by simp only [beq_eq_false_iff_ne]; exact hj1
  rw [h1'] at hc
  have hfp := checkWin_fpOne (hc 0 (Nat.zero_le _))
  have hall := honest_contracts_ext (L' := L') hfun hcan hrun h16' h32'
  obtain ⟨-, -, -, -, hpar, hbody⟩ := checkWinsB_run (S := honestSem hdr T n) (Prog := coreProgram)
    hc (End.fnOf_mem hlt) (End.coreOf_find h1 hlt) (End.certOf_pows_ok _) h32'
    (fun h ↦ by rw [← hfp] at h; cases h) (certByName_coreOf h1 hlt) (fun i ↦ (hall i).lt b)
    (End.jtHolds_of hjt) hE hpre.1 hpre.2.1 hpre.2.2
    (fun i' hi' h0 hl ↦ by
      by_cases h16'' : i + 1 = 16
      · obtain rfl : i = 15 := by omega
        exact End.knownB_vs (honest_vsKnown hfun hcan hrun) h16' h32' hpre.2.2 hi' h0
          (holdsListB_mono (relLB_le_rel _) _ id (fun _ h ↦ h) hl)
      · exact End.known_plain h1 hlt hj1 h16'' hi' h0)
    hsafe
  -- the frame's words are the call's
  have hT := hv
  rw [ht] at hT
  obtain ⟨fn, hf, hparT, -, -, -, -, -, -⟩ := hT
  obtain rfl : fn = coreOf (i + 1) := Option.some.inj (hf.symm.trans (by rw [hcore]; exact hfind))
  have hgood : (∃ σJ bufs kids es vs, I.t = .node f σJ bufs kids ∧
      walk σJ (coreOf (i + 1)).body = .ret es vs ∧ ∀ e ∈ es, e.HoldsB S rd σJ) ∨
      ∃ σJ, I.t = .phantom f σJ := Or.inl ⟨σ, bufs, kids, es, vs, ht, hw, hev⟩
  have hgp : ∀ a o : ℕ, gpow a * gpow o = gpow (a + o) := fun a o ↦ by rw [gpow, gpow, gpow, pow_add]
  have hfw : frameWords L' (gpow I.fp) 2 (coreOf (i + 1)).params.length = args := by
    rw [← hparT]
    refine List.ext_getElem (by simp [frameWords]) fun k hk1 hk2 ↦ ?_
    have hk : k < (coreOf (i + 1)).params.length := by simpa [frameWords] using hk1
    simp only [frameWords, List.getElem_map, List.getElem_range, wd]
    rw [hgp, hX.read _ _
      (B2C.readB_args hfun hH' (B2C.shareOk_of h1 hlt) (End.winOk_of h1 hlt) hI hj hgood k hk)]
    simp [ht, Tree.val]
  obtain ⟨-, -, -, -, -, hretc⟩ := hX.instRunsB (B2C.instB_runs h hname hH (I.t.total B2C.fs + 1) I hI
    (Nat.lt_succ_self _) hm args rets hv)
  obtain ⟨-, -, -, -, -, hnret⟩ := B2C.instKB_kids h hname hH hI hm hv
  have hlr : rets.length = (certOf (i + 1)).nret := hnret (i + 1) (by rw [ht]; exact hj)
  have hla : args.length = (coreOf (i + 1)).params.length := by rw [← hparT, List.length_map]
  have hfr : frameWords L' (gpow I.fp) (2 + (coreOf (i + 1)).params.length) (certOf (i + 1)).nret =
      rets := by
    refine List.ext_getElem (by simp [frameWords, hlr]) fun k hk1 hk2 ↦ ?_
    simp only [frameWords, List.getElem_map, List.getElem_range, wd]
    rw [hgp, ← hla, hretc k hk2]
    rfl
  have hval : Located.valAt L' f I.fp = valG L' (gpow I.fp) (certOf (i + 1)) := by
    unfold Located.valAt frameVal
    rw [← hcn, certByName_coreOf h1 hlt]
  refine ⟨coreOf (i + 1), by rw [hcore]; exact hfind, ?_, ?_⟩
  · rw [hval, hpar, hfw]
  · rw [hval]
    exact holdsListB_mono (fun _ _ _ h ↦ h) _ id (fun rs h ↦ h.trans hfr) hbody

include hfun hcan hname hH hrun hX h16' h32' in
/-- **The honest body at an honest frame, on the extension, for a function with no bounds or
semantic pairs in its precondition** (`honest_bodyAt_plain`). -/
theorem honest_bodyAt_plain_ext {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {j : ℕ} (hj : B2C.idxOf f = some j) (hj1 : j ≠ 1)
    (hplain : (certOf j).pre = [] ∧ (certOf j).mem = [] ∧ (certOf j).sem = [])
    {args rets : List E}
    (hv : I.t.ValidB S coreProgram (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read args rets) :
    Located.BodyAtB (honestSem hdr T n) L' f args rets I.fp := by
  obtain ⟨hp, hm, hs⟩ := hplain
  refine honest_bodyAt_ext hfun hcan hname hH hrun hX h16' h32' hI ht hj hj1 ⟨?_, ?_, ?_⟩ hv
  · rw [hp]; intro _ h; simp at h
  · rw [hm]; intro _ h; simp at h
  · rw [hs]; intro _ h; simp at h

include hfun hcan hname hH hrun hX h16' h32' in
/-- **`verify_sub`'s body at its honest frame, on the extension** (`honest_vs_bodyAt`). -/
theorem honest_vs_bodyAt_ext {P W : Inst} (hP : P ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {σP : Val} {bufs : List ℕ} {kids : List Tree} (hPt : P.t = .node "__loop5" σP bufs kids)
    {argsP retsP : List E}
    (hvP : P.t.ValidB S coreProgram (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read argsP retsP)
    (hexp : B1.ExpTables (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read (σP (V.n 16))
      (σP (V.n 6)))
    (hW : W ∈ honestInsts coreProgram B2C.fs B2C.H hdr T) {i : ℕ} (hk : P.t.kids[i]? = some W.t)
    (hVfp : P.kidFps[i]? = some W.fp) {σV : Val} {bufsV : List ℕ} {kidsV : List Tree}
    (hWt : W.t = .node "verify_sub" σV bufsV kidsV) {args rets : List E}
    (hvW : W.t.ValidB S coreProgram (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read args rets) :
    Located.BodyAtB (honestSem hdr T n) L' "verify_sub" args rets W.fp := by
  set L := honest coreProgram B2C.fs B2C.H B2C.C hdr T with hL
  have hvP' := hvP
  rw [hPt] at hvP' hk
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hvP'
  obtain rfl : fn = coreOf 36 := Option.some.inj
    (hf.symm.trans (by rw [← loop5_name]; exact End.coreOf_find (by decide) (by decide)))
  obtain ⟨c, hc, hcf, -⟩ := kid_call hkv hk hWt
  have hcm : c ∈ calls es := List.mem_of_getElem? hc
  have hargs : c.args = [.n 65, .n 66, .n 13, .n 14, .n 16, .n 6, .n 79] :=
    loop5_sites_vs _ (B2C.walk_sites (σ := σP) _ (by rw [hw]; exact hcm)) hcf
  have hF := (B2C.b2HypsB hfun).frame hdr rd T hname hH P hP "__loop5" σP bufs kids hPt 36
    idxOf_loop5 es vs hw
  obtain ⟨-, -, hka, -⟩ := hF.kid i c W.fp hc hVfp
  have r4 := hka 4 (by rw [hargs]; decide)
  have r5 := hka 5 (by rw [hargs]; decide)
  simp only [hargs] at r4 r5
  obtain ⟨hp, hm⟩ := vs_plain
  refine honest_bodyAt_ext hfun hcan hname hH hrun hX h16' h32' hW hWt idxOf_vs (by decide)
    ⟨by rw [hp]; intro _ h; simp at h, by rw [hm]; intro _ h; simp at h, ?_⟩ hvW
  have hsem : SemHolds glob L (gpow W.fp) (certOf 16).sem := by
    rw [End.vs_sem]
    intro p hp'
    simp only [List.mem_singleton] at hp'
    subst hp'
    show B1.ExpTables L.read (wd L (gpow W.fp) 6) (wd L (gpow W.fp) 7)
    have hgp : ∀ a o : ℕ, gpow a * gpow o = gpow (a + o) := fun a o ↦ by
      rw [gpow, gpow, gpow, pow_add]
    simp only [wd, hgp]
    rw [show W.fp + 6 = W.fp + (2 + 4) by omega, show W.fp + 7 = W.fp + (2 + 5) by omega, r4, r5]
    exact hexp
  exact hX.semHolds hsem

include hfun hcan hrun hX h16' h32' in
/-- **`main`'s body at its frame** (`0`) on the extension (`honest_main_bodyAt`). -/
theorem honest_main_bodyAt_ext :
    Located.BodyAtB (honestSem hdr T n) L' "main" [] [] 0 := by
  have hs : SafeB (honestSem hdr T n) guest L' n ⟨gpow 0, 1⟩ := by
    have := hX.safeB (honest_safe_initial hcan hrun)
    rwa [show (Regs.initial : Regs K) = ⟨gpow 0, 1⟩ by rw [gpow, pow_zero]; rfl] at this
  have hb := End.mainBodyLB_of_safe (honest_vsKnown hfun hcan hrun) (B1.expKnownB _) h16' h32' hs
  obtain ⟨-, -, -, -, -, hparams, hname'⟩ := End.main_facts
  have hval : Located.valAt L' "main" 0 = valG L' 1 (certOf 1) := by
    unfold Located.valAt frameVal
    rw [show (gpow 0 : K) = 1 by rw [gpow, pow_zero], ← hname', certByName_coreOf le_rfl (by decide)]
  refine ⟨coreOf 1, by rw [← hname']; exact End.coreOf_find le_rfl (by decide), ?_, ?_⟩
  · rw [hparams]; rfl
  · rw [hval]; exact hb

include hfun hname hH hX in
/-- **The decoder's valuation at an honest frame of the extension is the instance's**
(`honest_valAt`). -/
theorem honest_valAt_ext {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {j : ℕ} (hj : B2C.idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) {v : V} (hv : v ∈ B2C.namedOf (coreOf j).params es vs)
    (h2 : 2 ≤ B2C.cellJ j v) (hn : B2C.cellJ j v < B2C.fsN j) :
    Located.valAt L' f I.fp v = σ v := by
  rw [hX.valAt]
  exact honest_valAt hfun hname hH hI ht hj hw hv h2 hn

end Honest

end
end LeanVM.E2E.Complete
