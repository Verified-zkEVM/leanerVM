/-
  LeanVM.Guest.SoundB

  B2's soundness for the deployed bytecode under any semantics of `BLAKE2S`: every compiled
  function's contract from its checks, and `main`'s body at its frame from a halting run.
-/

module

public import LeanVM.Guest.SoundFacts
public import LeanVM.Guest.CheckSoundB

/-!
# B2 soundness under any `BLAKE2S` semantics

`Sound.lean` over `CheckSoundB.lean`. The checks are the deployed ones (`Checked.all_ok`,
`SoundFacts.lean`); a run under `S` gives each function's located core relation under `S`.

Two windows start from a semantic fact B1 proves of code run before them, and here those facts
are hypotheses, stated over `S` (B1's lemmas over a hash model discharge them):

* `VsKnownB S`: `verify_sub`'s first `1927` statements put `col_kappas`' entries among the `29`
  arms of `check_opening_terminal` (`B1.VerifySub.VsKnown` over `S`);
* `ExpKnownB S`: `exponent_tables` returns the exponent tables (`B1.exponent_tables_iff` over
  `S`; `exponent_tables` has no `BLAKE2S`, so `Core.relB_iff_rel_of_freeOn` gives it from the
  deployed lemma).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.Exec LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.EndToEnd

@[expose] public section

variable {S : BlakeSem}

/-! ## The facts of B1 the windows take -/

variable (S) in
/-- **`verify_sub`'s obligation under `S`** (`B1.VerifySub.VsKnown` over `S`): on every memory
of `2^κ` words, `16 ≤ κ ≤ 32`, over the exponent tables at `verify_sub`'s arguments `4`, `5`,
its first `1927` statements put `col_kappas`' entries among the `29` arms. -/
def VsKnownB : Prop :=
  ∀ rd : Reader, (∃ κ, 16 ≤ κ ∧ κ ≤ 32 ∧ ∃ L : MemImage κ, rd = L.read) → ∀ σ : Val,
    B1.ExpTables rd (σ (.n 4)) (σ (.n 5)) →
    Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ ((Fn.body Data.core15).take 1927) True
      (fun _ ↦ True) →
      ∀ c < 92, ∃ e < 29, LoadHolds rd (σ (.n 1631)) c (ofK (gpow e))

variable (S) in
/-- **`exponent_tables`' meaning under `S`** (`B1.exponent_tables_iff`, its soundness): what
`main`'s second window starts from. -/
def ExpKnownB : Prop :=
  ∀ (rd : Reader) (p q : E), coreProgram.RelB S rd "exponent_tables" [] [p, q] → B1.ExpTables rd p q

/-! ## `verify_sub`'s obligation -/

theorem knownB_vs (hvs : VsKnownB S) {κ : ℕ} {L : MemImage κ} (h16 : minLogMem ≤ κ)
    (h32 : κ ≤ maxLogMem) {fp : K} (hsem : SemHolds glob L fp (certOf 16).sem) {i : ℕ}
    (hi : i ≤ (certOf 16).cuts.length) (h0 : 0 < i)
    (hl : Stmt.HoldsListB S (coreProgram.RelB S L.read) L.read (valG L fp (certOf 16))
      ((coreOf 16).body.take ((certOf 16).cutAt i).start) True (fun _ ↦ True)) :
    MemKnown L fp ((certOf 16).cutAt i).known ∧ SemHolds glob L fp ((certOf 16).cutAt i).sems := by
  obtain rfl : i = 1 := by rw [vs_cuts] at hi; omega
  obtain ⟨hst, hkn, hsm⟩ := vs_cut
  obtain ⟨c4, c5, c1631⟩ := vs_cells
  rw [hkn, hsm]
  refine ⟨fun m hm c hc ↦ ?_, fun _ h ↦ by simp at h⟩
  simp only [List.mem_singleton] at hm
  subst hm
  rw [hst, coreOf_16] at hl
  have ht : B1.ExpTables L.read (valG L fp (certOf 16) (.n 4)) (valG L fp (certOf 16) (.n 5)) := by
    have := hsem (6, 7) (by rw [vs_sem]; exact List.mem_singleton_self _)
    simp only [valG, c4, c5]
    exact this
  have := hvs L.read ⟨κ, h16, h32, L, rfl⟩ _ ht hl c hc
  simpa only [valG, Core.V.idx, c1631] using this

/-! ## `main`'s obligation -/

theorem knownB_main (hexp : ExpKnownB S) {κ : ℕ} {L : MemImage κ} {fp : K} {i : ℕ} (hi : i ≤ (certOf 1).cuts.length)
    (h0 : 0 < i)
    (hl : Stmt.HoldsListB S (coreProgram.RelB S L.read) L.read (valG L fp (certOf 1))
      ((coreOf 1).body.take ((certOf 1).cutAt i).start) True (fun _ ↦ True)) :
    MemKnown L fp ((certOf 1).cutAt i).known ∧ SemHolds glob L fp ((certOf 1).cutAt i).sems := by
  obtain ⟨hlen, hkn, hsm⟩ := main_cut
  obtain rfl : i = 1 := by rw [hlen] at hi; omega
  rw [hkn, hsm]
  refine ⟨fun _ h ↦ by simp at h, fun p hp ↦ ?_⟩
  simp only [List.mem_singleton] at hp
  subst hp
  have hnr : Stmt.noRetList ((coreOf 1).body.take (((certOf 1).cutAt 1).start - 1)) = true := by
    decide +kernel
  rw [main_call, holdsListB_append] at hl
  have hcall := ((holdsListB_noRet _ hnr _ _).mp hl).2
  simp only [Stmt.HoldsListB, Stmt.HoldsB, List.map_cons, List.map_nil] at hcall
  exact hexp L.read _ _ hcall.1

/-! ## The contracts -/

/-- **B2's step**: each contract for runs shorter than `n + 1`, given all of them for runs
shorter than `n`. -/
theorem b2B_step (hvs : VsKnownB S) :
    ∀ {κ : ℕ} (L : MemImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ n,
      (∀ j, FunSpecLtB S guest L n (glob.sig j).entry (Check.Pre glob L j)
        (Check.PostB S coreProgram glob L certByName j)) →
      ∀ i, FunSpecLtB S guest L (n + 1) (glob.sig i).entry (Check.Pre glob L i)
        (Check.PostB S coreProgram glob L certByName i) := by
  intro κ L h16 h32 n hlt j fp k hk hpre hsafe
  obtain ⟨hgood, hjt, henv, hbnd, hmem, hsem⟩ := hpre
  have hj : 2 ≤ j ∧ j < nFns := by simpa [glob, good] using hgood
  have hc := winOk_of (j := j) (by omega) hj.2
  have h1 : (j == 1) = false := by simp; omega
  rw [h1] at hc
  have hfp := checkWin_fpOne (hc 0 (Nat.zero_le _))
  obtain ⟨hrel, hpost, hret, -⟩ := checkWinsB_run (Prog := coreProgram) hc (fnOf_mem hj.2)
    (coreOf_find (by omega) hj.2) (certOf_pows_ok j) h32 (fun h ↦ by rw [← hfp] at h; cases h)
    (certByName_coreOf (by omega) hj.2)
    (fun i ↦ (hlt i).mono (by omega)) hjt henv hbnd hmem hsem
    (fun i hi h0 hl ↦ by
      by_cases h16 : j = 16
      · subst h16
        exact knownB_vs hvs h16 h32 hsem hi h0
          (holdsListB_mono (relLB_le_rel _) _ id (fun _ h ↦ h) hl)
      · exact known_plain (by omega) hj.2 (by omega) h16 hi h0)
    hsafe
  obtain ⟨k', hk', r, hr, hs⟩ := hret rfl
  exact ⟨k', hk', r, hr, ⟨hrel, hpost⟩, hs⟩

/-- **B2 at `main`, located**: a halting run from `main`'s entry at `fp = 1`, the jump table
written and every contract holding for runs shorter than it, gives `main`'s body under its frame's
valuation, its calls located. -/
theorem b2B_mainL (hexp : ExpKnownB S) :
    ∀ {κ : ℕ} (L : MemImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → JumpTables L → ∀ k,
      (∀ j, FunSpecLtB S guest L k (glob.sig j).entry (Check.Pre glob L j)
        (Check.PostB S coreProgram glob L certByName j)) →
      SafeB S guest L k ⟨gpow mainEntry, 1⟩ →
        Stmt.HoldsListB S (RLB S coreProgram L certByName) L.read (valG L 1 (certOf 1)) (coreOf 1).body
          False (fun rs ↦ rs = []) := by
  intro κ L _ h32 hjtab k hlt hsafe
  have hc := winOk_of (j := 1) le_rfl (by decide)
  obtain ⟨henv, hpre, hmem, hsem, hnret, hparams, hname⟩ := main_facts
  obtain ⟨-, -, -, -, -, hbody⟩ := checkWinsB_run (Prog := coreProgram) (fp := 1) hc
    (fnOf_mem (by decide)) (coreOf_find le_rfl (by decide)) (certOf_pows_ok 1) h32 (fun _ ↦ rfl)
    (certByName_coreOf le_rfl (by decide)) hlt
    (jtHolds_of hjtab) (by rw [Facts.entryEnv, henv]; exact EnvHolds.nil)
    (by rw [hpre]; intro _ h; simp at h) (by rw [hmem]; intro _ h; simp at h)
    (by rw [hsem]; intro _ h; simp at h)
    (fun i hi h0 hl ↦ knownB_main hexp hi h0 (holdsListB_mono (relLB_le_rel _) _ id (fun _ h ↦ h) hl))
    (by rw [fnOf_1]; exact hsafe)
  rw [hnret] at hbody
  exact hbody

/-- **B2 at `main`**: a halting run from `main`'s entry at `fp = 1`, the jump table written and
every contract holding for runs shorter than it, gives `main`'s relation. -/
theorem b2B_main (hexp : ExpKnownB S) :
    ∀ {κ : ℕ} (L : MemImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → JumpTables L → ∀ k,
      (∀ j, FunSpecLtB S guest L k (glob.sig j).entry (Check.Pre glob L j)
        (Check.PostB S coreProgram glob L certByName j)) →
      SafeB S guest L k ⟨gpow mainEntry, 1⟩ → coreProgram.RelB S L.read "main" [] [] := by
  intro κ L _ h32 hjtab k hlt hsafe
  have hc := winOk_of (j := 1) le_rfl (by decide)
  obtain ⟨henv, hpre, hmem, hsem, hnret, hparams, hname⟩ := main_facts
  obtain ⟨hrel, -⟩ := checkWinsB_run (Prog := coreProgram) (fp := 1) hc (fnOf_mem (by decide))
    (coreOf_find le_rfl (by decide)) (certOf_pows_ok 1) h32 (fun _ ↦ rfl)
    (certByName_coreOf le_rfl (by decide)) hlt
    (jtHolds_of hjtab) (by rw [Facts.entryEnv, henv]; exact EnvHolds.nil)
    (by rw [hpre]; intro _ h; simp at h) (by rw [hmem]; intro _ h; simp at h)
    (by rw [hsem]; intro _ h; simp at h)
    (fun i hi h0 hl ↦ knownB_main hexp hi h0 (holdsListB_mono (relLB_le_rel _) _ id (fun _ h ↦ h) hl))
    (by rw [fnOf_1]; exact hsafe)
  rw [hname, hparams, hnret] at hrel
  exact relLB_le_rel _ _ _ _ hrel

/-! ## The run's start, and `main` at its frame (`End.lean`, `EndLoc.lean`) -/

/-- **The run's start, soundly, under `S`**: a halting run from `(g^0, 1)` writes the jump table
and halts from `main`'s entry at `fp = 1` (`safe_jumpTables`). -/
theorem safeB_jumpTables {κ : ℕ} {L : MemImage κ} {k : ℕ} (h : SafeB S guest L k ⟨gpow 0, 1⟩) :
    JumpTables L ∧ ∃ k', SafeB S guest L k' ⟨gpow mainEntry, 1⟩ := by
  have hwalk : ∀ i ≤ Data.f0.len, (∀ j < i, HoldsB S L j 1 (Data.f0.instrAt j)) ∧
      ∃ k', SafeB S guest L k' ⟨gpow i, 1⟩ := by
    intro i
    induction i with
    | zero => exact fun _ ↦ ⟨fun _ hj ↦ absurd hj (Nat.not_lt_zero _), k, h⟩
    | succ i ih =>
      intro hi
      obtain ⟨hh, k', hk'⟩ := ih (by omega)
      obtain ⟨o, k0, k1, k2, hins, -⟩ := f0_instr (show i < Data.f0.len by omega)
      have hf := f0_fetch (show i < Data.f0.len by omega)
      rw [hins] at hf
      obtain ⟨k'', -, hH, hs⟩ := hk'.fallThrough hf (f0_pc_lt (by omega)) rfl
      refine ⟨fun j hj ↦ ?_, k'', hs⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hh j hj
      · rw [hins]; exact hH
  obtain ⟨hh, hrun⟩ := hwalk _ le_rfl
  refine ⟨fun q hq ↦ ?_, hrun⟩
  obtain ⟨ins, hmem, hq⟩ := List.mem_filterMap.mp (tableCells_eq ▸ hq)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  have hlen : i < Data.f0.len := CompiledFn.length_code (CompiledFn.wellChunked_of_mem f0_mem) ▸ hi
  have hc := CompiledFn.getElem?_code (CompiledFn.wellChunked_of_mem f0_mem) hlen
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hc
  obtain ⟨o, k0, k1, k2, hins, -⟩ := f0_instr hlen
  have hH := hh i hlen
  rw [hc, hins] at hq
  rw [hins] at hH
  simp only [setCell?, Option.some.injEq] at hq
  subst hq
  rw [← gpow_mul_one]
  exact hH

/-- **B2 at `main`, located, under `S`, for a halting run from `(g^0, 1)`**
(`mainBodyL_of_safe`). -/
theorem mainBodyLB_of_safe (hvs : VsKnownB S) (hexp : ExpKnownB S) {κ : ℕ} {L : MemImage κ}
    (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem) {k : ℕ} (hs : SafeB S guest L k ⟨gpow 0, 1⟩) :
    Stmt.HoldsListB S (RLB S coreProgram L certByName) L.read (valG L 1 (certOf 1)) (coreOf 1).body
      False (fun rs ↦ rs = []) := by
  obtain ⟨hjt, k', hk'⟩ := safeB_jumpTables hs
  have hall : ∀ j, FunSpecB S guest L (glob.sig j).entry (Check.Pre glob L j)
      (Check.PostB S coreProgram glob L certByName j) :=
    funSpecB_induction (P := fun j ↦ Check.Pre glob L j)
      (Q := fun j ↦ Check.PostB S coreProgram glob L certByName j)
      (b2B_step hvs L h16 h32)
  exact b2B_mainL hexp L h16 h32 hjt k' (fun j ↦ (hall j).lt k') hk'

/-- **B2 at `main`, located, under `S`, for a valid execution** (`mainBodyL_of`): `main`'s body
under its frame's valuation, its calls located, under `S`; and the public input's cells at `g^0`,
`g^1`. -/
theorem mainBodyLB_of (hvs : VsKnownB S) (hexp : ExpKnownB S) {input : PublicInput}
    {t : Trace guest} (hv : ValidExecutionB S guest input t) :
    Stmt.HoldsListB S (RLB S coreProgram t.image certByName) t.image.read
      (valG t.image 1 (certOf 1)) (coreOf 1).body False (fun rs ↦ rs = []) ∧
    t.image.read 1 = some (digestScalars (publicDigest input)).1 ∧
    t.image.read g = some (digestScalars (publicDigest input)).2 := by
  have hs := safeB_of_validExecution hv
  obtain ⟨⟨h16, h32, h0, h1⟩, -⟩ := hv
  have hd := Complete.digestScalars_publicDigest input
  exact ⟨mainBodyLB_of_safe hvs hexp h16 h32 hs, by rw [hd, ← pow_zero g]; exact h0,
    by rw [hd, ← pow_one g]; exact h1⟩

end
end LeanVM.Guest.End
