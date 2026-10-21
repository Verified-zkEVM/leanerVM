/-
  LeanVM.E2E.Complete.HonestBodies

  The honest execution decodes at the honest frames: under the table semantics of the honest run's
  own rows, the guest's code holds at every honest instance's frame (`BodyAtB`), for the functions
  whose precondition holds there.
-/

module

public import LeanVM.Guest.B2C.RunsOn
public import LeanVM.E2E.Complete.FunModel
public import LeanVM.Guest.B1.Tables.GuestHypsM
public import LeanVM.Guest.B1.VerifySub.KnownB
public import LeanVM.Guest.Located.BasicB

/-!
# The honest bodies under the run's own rows

T6-det's decoding (L9, `DecodeHonest`) reads the honest execution's memory under the table
semantics of its own rows, `S' = tableSem (t.blakeRows blakeFree)` (decision E2E-3), at the frames
the idealized proof names (E2E-5): it needs `Located.BodyAtB S' L f args rets a` at the honest
frame `a` of each decoded call (`Located.frameOfB_of_bodyAt`).

The tree of the guest's completeness only gives checks under the completeness model's semantics
`S`; that each of its `BLAKE2S` atoms is a row the run executes is a soundness fact. So the bodies
come from B2's soundness (`Check.checkWinsB_run`) under `S'`, at the honest frames:

* **the run is valid under `S'`**, its rows being rows of `S` of canonical cells
  (`runB_of_runRows`);
* **the contracts hold under `S'`** (`honest_contracts`): `S'` is functional (`S` is, and `S'`
  accepts only rows of `S`), so it is the semantics of a hash model (`HashModel.ofFunctional`), and
  T2's facts over every hash model give `verify_sub`'s windows' obligation (`End.VsKnownB S'`,
  `vsKnownB_model`); then `End.b2B_step` by induction;
* **every honest node instance is entered on the halting run** (`B2C.honest_onRun`, from the
  completeness walk keeping the callees' entries on the run, `KidsOn`), so the run from its entry
  at its frame halts under `S'` (`safe_tableSem_of_segment`: a segment's rows are the run's);
* **its precondition holds at its frame**: the self frame pointer cells and the jump table from the
  honest memory; the bounds and semantic pairs (`pre`, `mem`, `sem`), empty for all but eight
  functions, as a hypothesis (`honest_bodyAt`), discharged when empty (`honest_bodyAt_plain`).

Then the body holds at the frame under `S'` on the frame's words, which are the instance's
arguments and returns (`readB_args`, the returns left after the arguments).

* `honest_bodyAt`, `honest_bodyAt_plain`: `BodyAtB S' L f args rets I.fp` at an honest node instance
  of function `j ≠ 1`;
* `honest_main_bodyAt`: `main`'s body at frame `0`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check LeanVM.Guest.Value
open LeanVM.Guest.End (mainEntry JumpTables)
open LeanVM.Guest.Exec (index EnvHolds envOf Sym)

@[expose] public section

/-! ## A segment of a run under the run's own rows -/

/-- The rows of a run are the rows of its first part and of the rest. -/
theorem runRows_add {S : BlakeSem} {κ : ℕ} {prog : Semantics.Program} {L : MemImage κ} :
    ∀ {a : ℕ} {r X : Regs K}, runB S prog L a r = some X → ∀ b,
      runRows S prog L (a + b) r = runRows S prog L a r ++ runRows S prog L b X
  | 0, r, X, h, b => by
    simp only [runB, Option.some.injEq] at h
    subst h
    simp [runRows]
  | a + 1, r, X, h, b => by
    by_cases hpc : r.pc = prog.finalPc
    · simp [runB, hpc] at h
    simp only [runB, hpc, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨r', hs, hrun⟩ := h
    obtain ⟨i, hf, -⟩ := Option.bind_eq_some_iff.mp hs
    rw [show a + 1 + b = (a + b) + 1 by omega, runRows_succ hpc hf hs, runRows_succ hpc hf hs,
      runRows_add hrun b, List.append_assoc]

/-- **A segment of a halting run halts under the run's own table**: from a state the halting run
passes, the rest of it is a run under the table semantics of its Flock-blind rows. -/
theorem safe_tableSem_of_segment {S : BlakeSem} (hS : ∀ b, S.row b → blakeFree.row b) {κ : ℕ}
    {prog : Semantics.Program} {L : MemImage κ} {n a b : ℕ} {X : Regs K}
    (hn : runB S prog L n Regs.initial = some (Regs.final prog))
    (ha : runB S prog L a Regs.initial = some X) (hb : runB S prog L b X = some (Regs.final prog)) :
    runB (tableSem (runRows blakeFree prog L n Regs.initial)) prog L b X = some (Regs.final prog) := by
  have hab : runB S prog L (a + b) Regs.initial = some (Regs.final prog) := by
    rw [LeanVM.Guest.runB_add (S := S) a b, ha]
    exact hb
  obtain rfl := steps_unique hn hab
  refine runB_of_runRows (S := S) (fun row hrow hc ↦ ⟨hS row hc, ?_⟩) hb
  rw [runRows_eq_of_runB hS hab, runRows_add ha b]
  exact List.mem_append_right _ hrow

/-- **The table of a run of a functional semantics is functional.** -/
theorem functional_tableSem {S : BlakeSem} (hfun : B2C.SemFunctional S) {rows : List BlakeRow}
    (h : ∀ b ∈ rows, S.row b) : Functional (tableSem rows) :=
  fun h1 h2 ↦ hfun (h _ h1.2) (h _ h2.2)

/-! ## The honest run's table -/

/-- **The honest run's table semantics**: of the Flock-blind rows of the honest memory's run of
`n` steps (`DecodeHonest`'s semantics). -/
noncomputable abbrev honestSem (hdr : E × E) (T : Tree) (n : ℕ) : BlakeSem :=
  tableSem (Trace.blakeRows blakeFree
    (⟨_, honest coreProgram B2C.fs B2C.H B2C.C hdr T, n⟩ : Trace guest))

section Honest

variable {S : BlakeSem} (hfun : B2C.SemFunctional S)
  (hcan : ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
    CanonicalCells m cv0 cv1 o0 o1 md)
  {hdr : E × E} {rd : Reader} {T : Tree} (hname : T.name = "main")
  (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])
  {n : ℕ} (hrun : runB S guest (honest coreProgram B2C.fs B2C.H B2C.C hdr T) n Regs.initial =
    some (Regs.final guest))
include hcan hrun

/-- The honest run's table holds rows of `S` only. -/
theorem honestSem_rows : ∀ b ∈ Trace.blakeRows blakeFree
    (⟨_, honest coreProgram B2C.fs B2C.H B2C.C hdr T, n⟩ : Trace guest), S.row b := by
  intro b hb
  unfold Trace.blakeRows at hb
  rw [runRows_eq_of_runB (S' := blakeFree) (fun _ hc ↦ hcan hc) hrun] at hb
  exact row_of_mem_runRows hb

include hfun in
/-- **The honest run's table semantics is a hash model's**, functional and of canonical cells. -/
noncomputable def honestModel : HashModel :=
  HashModel.ofFunctional (honestSem hdr T n)
    (functional_tableSem hfun (honestSem_rows hcan hrun)) (fun hc ↦ hc.1)

include hfun in
theorem honestModel_sem : (honestModel hfun hcan hrun).sem = honestSem hdr T n := rfl

/-- **The halting run is a run under the run's own table.** -/
theorem honest_safe_initial :
    runB (honestSem hdr T n) guest (honest coreProgram B2C.fs B2C.H B2C.C hdr T) n Regs.initial =
      some (Regs.final guest) :=
  runB_of_runRows (S := S) (fun b hb hc ↦ ⟨hcan hc, by
    show b ∈ runRows blakeFree guest _ n Regs.initial
    rw [runRows_eq_of_runB (S' := blakeFree) (fun _ hc ↦ hcan hc) hrun]
    exact hb⟩) hrun

omit hcan hrun in
include hH in
/-- The honest memory has between `2^16` and `2^32` words. -/
theorem honest_logMem : minLogMem ≤ logMem (T.total B2C.fs) ∧ logMem (T.total B2C.fs) ≤ maxLogMem :=
  ⟨minLogMem_le_logMem _, hH.toHonestB.logMem_le⟩

include hfun hH in
/-- **Every contract holds under the honest run's table**: B2's soundness under it, its windows'
obligation from T2's facts over its hash model. -/
theorem honest_contracts (j : ℕ) :
    FunSpecB (honestSem hdr T n) guest (honest coreProgram B2C.fs B2C.H B2C.C hdr T)
      (glob.sig j).entry (Pre glob (honest coreProgram B2C.fs B2C.H B2C.C hdr T) j)
      (PostB (honestSem hdr T n) coreProgram glob (honest coreProgram B2C.fs B2C.H B2C.C hdr T)
        certByName j) := by
  have hvs : End.VsKnownB (honestSem hdr T n) :=
    B1.VerifySub.vsKnownB_model (M := honestModel hfun hcan hrun)
      (B1.VerifySub.guestHypsM_gkr _) (B1.VerifySub.guestHypsM_tables _)
  obtain ⟨h16, h32⟩ := honest_logMem hH
  exact funSpecB_induction (End.b2B_step hvs _ h16 h32) j

include hfun in
/-- **`verify_sub`'s windows' obligation under the honest run's table**, from T2's facts over its
hash model. -/
theorem honest_vsKnown : End.VsKnownB (honestSem hdr T n) :=
  B1.VerifySub.vsKnownB_model (M := honestModel hfun hcan hrun)
    (B1.VerifySub.guestHypsM_gkr _) (B1.VerifySub.guestHypsM_tables _)

include hfun hname hH in
/-- **The honest body at an honest frame**: at an honest node instance of a function `j ≠ 1`,
valid on the honest memory's words on its call's words, the precondition's bounds and semantic
pairs holding at its frame, the guest's code for it holds there under the honest run's table, on
those words (`Located.BodyAtB`). -/
theorem honest_bodyAt {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {j : ℕ} (hj : B2C.idxOf f = some j) (hj1 : j ≠ 1)
    (hpre : BndHolds (honest coreProgram B2C.fs B2C.H B2C.C hdr T) (gpow I.fp) (certOf j).pre ∧
      MemPre (honest coreProgram B2C.fs B2C.H B2C.C hdr T) (gpow I.fp) (certOf j).mem ∧
      SemHolds glob (honest coreProgram B2C.fs B2C.H B2C.C hdr T) (gpow I.fp) (certOf j).sem)
    {args rets : List E}
    (hv : I.t.ValidB S coreProgram (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read args rets) :
    Located.BodyAtB (honestSem hdr T n) (honest coreProgram B2C.fs B2C.H B2C.C hdr T) f args rets
      I.fp := by
  set L := honest coreProgram B2C.fs B2C.H B2C.C hdr T with hL
  have h := B2C.b2HypsB hfun
  obtain ⟨i, rfl, hi, hn', hfind, hcore, -, -, h1, hlt⟩ := B2C.fn_of_idx hj
  have hcn : (coreOf (i + 1)).name = f := by rw [hcore]; exact hn'
  -- on the run
  obtain ⟨-, hm, hon0, r, -, hon1, hon2⟩ := B2C.honest_onRun h hname hH I hI f σ bufs kids ht
  have hjt : JumpTables L := B2C.jumpTablesB_honestC hH.toHonestB hname
  have hpro : ReachB S guest L Regs.initial ⟨gpow mainEntry, 1⟩ := by
    have := (B2C.runCB_jumpTables (S := S) hjt).reach
    rwa [show (⟨gpow 0, 1⟩ : Regs K) = Regs.initial by rw [gpow, pow_zero]; rfl] at this
  have hent : B2C.entryOf I.t.name = (fnOf (i + 1)).entry := by rw [ht]; exact B2C.entryOf_of hj
  obtain ⟨a, ha⟩ := hpro.trans hon0
  obtain ⟨b, hb⟩ := hon1.trans hon2
  rw [hent] at ha hb
  have hsafe : SafeB (honestSem hdr T n) guest L b ⟨gpow (fnOf (i + 1)).entry, gpow I.fp⟩ :=
    safe_tableSem_of_segment (fun _ hc ↦ hcan hc) hrun ha hb
  -- the frame
  have hH' := hH.toHonestB
  obtain ⟨es, vs, hw, hev, -⟩ := B2C.nodeB_valid ht hj (instsB_good T 0 hdr hH'.valid I hI)
  have hF := h.frame hdr rd T hname hH I hI f σ bufs kids ht (i + 1) hj es vs hw
  have hc0 := B2C.Cplw.cplOk_all (i + 1) h1 hlt 0 (Nat.zero_le _) 0 (B2C.one_le_nParts (i + 1) 0)
  have hw0 := B2C.winOkC_of hc0
  simp only [B2C.winOkC, Bool.and_eq_true, Nat.beq_refl, Bool.cond_true] at hw0
  have henv := hw0.2.2
  have hX := B2C.cxOk hF (End.certOf_pows_ok (i + 1)) (index (B2C.segsW (i + 1) 0))
    (B2C.clocW (certOf (i + 1)) 0) (B2C.nvOf (B2C.partStmts (i + 1) 0 0) 0) none
  have hE : EnvHolds L (gpow I.fp) (envOf (certOf (i + 1)).facts.env) := by
    refine envOf_holds fun p hp ↦ ?_
    have := List.all_eq_true.mp henv p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨h1', h2'⟩ := this
    have := hX.stat p.1 _ h2'
    rw [Sym.beq_eq h1']
    simp only [B2C.PC.word, Nat.add_zero] at this
    simpa [Sym.val, B2C.gpow_addC] using this
  -- B2's soundness at the frame
  have hc := End.winOk_of h1 hlt
  have h1' : ((i + 1) == 1) = false := by simp only [beq_eq_false_iff_ne]; exact hj1
  rw [h1'] at hc
  have hfp := checkWin_fpOne (hc 0 (Nat.zero_le _))
  obtain ⟨h16, h32⟩ := honest_logMem hH
  have hall := honest_contracts hfun hcan hH hrun
  obtain ⟨-, -, -, -, hpar, hbody⟩ := checkWinsB_run (S := honestSem hdr T n) (Prog := coreProgram)
    hc (End.fnOf_mem hlt) (End.coreOf_find h1 hlt) (End.certOf_pows_ok _) h32
    (fun h ↦ by rw [← hfp] at h; cases h) (certByName_coreOf h1 hlt) (fun i ↦ (hall i).lt b)
    (End.jtHolds_of hjt) hE hpre.1 hpre.2.1 hpre.2.2
    (fun i' hi' h0 hl ↦ by
      by_cases h16' : i + 1 = 16
      · obtain rfl : i = 15 := by omega
        exact End.knownB_vs (honest_vsKnown hfun hcan hrun) h16 h32 hpre.2.2 hi' h0
          (holdsListB_mono (relLB_le_rel _) _ id (fun _ h ↦ h) hl)
      · exact End.known_plain h1 hlt hj1 h16' hi' h0)
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
  have hfw : frameWords L (gpow I.fp) 2 (coreOf (i + 1)).params.length = args := by
    rw [← hparT]
    refine List.ext_getElem (by simp [frameWords]) fun k hk1 hk2 ↦ ?_
    have hk : k < (coreOf (i + 1)).params.length := by simpa [frameWords] using hk1
    simp only [frameWords, List.getElem_map, List.getElem_range, wd]
    rw [hgp, B2C.readB_args hfun hH' (B2C.shareOk_of h1 hlt) (End.winOk_of h1 hlt) hI hj hgood k hk]
    simp [ht, Tree.val]
  obtain ⟨-, -, -, -, -, hretc⟩ := B2C.instB_runs h hname hH (I.t.total B2C.fs + 1) I hI
    (Nat.lt_succ_self _) hm args rets hv
  obtain ⟨-, -, -, -, -, hnret⟩ := B2C.instKB_kids h hname hH hI hm hv
  have hlr : rets.length = (certOf (i + 1)).nret := hnret (i + 1) (by rw [ht]; exact hj)
  have hla : args.length = (coreOf (i + 1)).params.length := by rw [← hparT, List.length_map]
  have hfr : frameWords L (gpow I.fp) (2 + (coreOf (i + 1)).params.length) (certOf (i + 1)).nret =
      rets := by
    refine List.ext_getElem (by simp [frameWords, hlr]) fun k hk1 hk2 ↦ ?_
    simp only [frameWords, List.getElem_map, List.getElem_range, wd]
    rw [hgp, ← hla, hretc k hk2]
    rfl
  have hval : Located.valAt L f I.fp = valG L (gpow I.fp) (certOf (i + 1)) := by
    unfold Located.valAt frameVal
    rw [← hcn, certByName_coreOf h1 hlt]
  refine ⟨coreOf (i + 1), by rw [hcore]; exact hfind, ?_, ?_⟩
  · rw [hval, hpar, hfw]
  · rw [hval]
    exact holdsListB_mono (fun _ _ _ h ↦ h) _ id (fun rs h ↦ h.trans hfr) hbody

include hfun hname hH in
/-- **The honest body at an honest frame, for a function with no bounds or semantic pairs in its
precondition** (all but eight of the guest's functions; `honest_bodyAt`). -/
theorem honest_bodyAt_plain {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {j : ℕ} (hj : B2C.idxOf f = some j) (hj1 : j ≠ 1)
    (hplain : (certOf j).pre = [] ∧ (certOf j).mem = [] ∧ (certOf j).sem = [])
    {args rets : List E}
    (hv : I.t.ValidB S coreProgram (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read args rets) :
    Located.BodyAtB (honestSem hdr T n) (honest coreProgram B2C.fs B2C.H B2C.C hdr T) f args rets
      I.fp := by
  obtain ⟨hp, hm, hs⟩ := hplain
  refine honest_bodyAt hfun hcan hname hH hrun hI ht hj hj1 ⟨?_, ?_, ?_⟩ hv
  · rw [hp]; intro _ h; simp at h
  · rw [hm]; intro _ h; simp at h
  · rw [hs]; intro _ h; simp at h

include hfun hH in
/-- **`main`'s body at its frame** (`0`) under the honest run's table. -/
theorem honest_main_bodyAt :
    Located.BodyAtB (honestSem hdr T n) (honest coreProgram B2C.fs B2C.H B2C.C hdr T) "main" [] []
      0 := by
  obtain ⟨h16, h32⟩ := honest_logMem hH
  have hs : SafeB (honestSem hdr T n) guest (honest coreProgram B2C.fs B2C.H B2C.C hdr T) n
      ⟨gpow 0, 1⟩ := by
    have := honest_safe_initial hcan hrun
    rwa [show (Regs.initial : Regs K) = ⟨gpow 0, 1⟩ by rw [gpow, pow_zero]; rfl] at this
  have hb := End.mainBodyLB_of_safe (honest_vsKnown hfun hcan hrun) (B1.expKnownB _) h16 h32 hs
  obtain ⟨-, -, -, -, -, hparams, hname'⟩ := End.main_facts
  have hval : Located.valAt (honest coreProgram B2C.fs B2C.H B2C.C hdr T) "main" 0 =
      valG (honest coreProgram B2C.fs B2C.H B2C.C hdr T) 1 (certOf 1) := by
    unfold Located.valAt frameVal
    rw [show (gpow 0 : K) = 1 by rw [gpow, pow_zero], ← hname', certByName_coreOf le_rfl (by decide)]
  refine ⟨coreOf 1, by rw [← hname']; exact End.coreOf_find le_rfl (by decide), ?_, ?_⟩
  · rw [hparams]; rfl
  · rw [hval]; exact hb

end Honest

end
end LeanVM.E2E.Complete
