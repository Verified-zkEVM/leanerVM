/-
  LeanVM.Guest.Sound

  B2's soundness for the deployed bytecode: every compiled function's contract from its checks,
  and `main`'s relation from a halting run of it.
-/

module

public import LeanVM.Guest.SoundFacts

/-!
# B2 soundness

The contracts are checker K's over `glob`: function `j`'s entry, `Check.Pre glob L j` and
`Check.Post coreProgram glob L certByName j`.

* `b2_step`: a function's contract for runs shorter than `n + 1`, given every contract for runs
  shorter than `n` (`checkWins_run` on its checked windows, `Checked.all_ok`). Each window after
  the first takes its memory bounds and semantic pairs from the statements before it: none but in
  `verify_sub` (function `19`), whose second window, before `check_opening_terminal`, takes the
  bound of the `99` column logs `col_kappas` holds from `VsKnown`, over the exponent tables its
  precondition carries.
* `b2_main`: `main`'s relation from a halting run from its entry at `fp = 1`, the jump table
  written. Its second window starts after `exponent_tables`, whose returns it knows to be the
  tables (`ExpTablesSound`).

`VsKnown` and `ExpTablesSound` are statements about the core IR alone (`coreProgram.Rel`), B1's
to prove (`verify_sub`'s callees `verify_tables` and `certify_placement`, and `exponent_tables`):
the theorems here take them as hypotheses.

Names are unique in `coreProgram` (`coreProgram_find_getElem`), and the jump table the checks
read is the one `__jump_tables` writes (`JumpTable.jt_of_jumpTables`). The certificates' facts
are `SoundFacts.lean`'s.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.Exec

@[expose] public section

/-! ## B1's obligations -/

/-- **`verify_sub`'s obligation** (B1's): on every memory image, over the exponent tables at
`verify_sub`'s arguments `4`, `5`, its first `2098` statements, up to its call of
`check_opening_terminal`, put the `99` entries of `col_kappas` (the value `1889`) among the `29`
arms of `column_selector`. -/
def VsKnown : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ σ : Val,
    B1.ExpTables L.read (σ (.n 4)) (σ (.n 5)) →
    Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf 19).body.take 2098) True (fun _ ↦ True) →
      ∀ c < 99, ∃ e < 29, LoadHolds L.read (σ (.n 1889)) c (ofK (gpow e))

/-- **`exponent_tables`' relation** (B1's): its two returned pointers hold the exponent tables. -/
def ExpTablesSound : Prop :=
  ∀ (rd : Reader) (p q : E), coreProgram.Rel rd "exponent_tables" [] [p, q] → B1.ExpTables rd p q

/-! ## `verify_sub`'s obligation -/

theorem known_vs (hvs : VsKnown) {κ : ℕ} {L : MemoryImage κ} (h16 : minLogMem ≤ κ)
    (h32 : κ ≤ maxLogMem) {fp : K} (hsem : SemHolds glob L fp (certOf 19).sem) {i : ℕ}
    (hi : i ≤ (certOf 19).cuts.length) (h0 : 0 < i)
    (hl : Stmt.HoldsList (coreProgram.Rel L.read) L.read (valG L fp (certOf 19))
      ((coreOf 19).body.take ((certOf 19).cutAt i).start) True (fun _ ↦ True)) :
    MemKnown L fp ((certOf 19).cutAt i).known ∧ SemHolds glob L fp ((certOf 19).cutAt i).sems := by
  obtain rfl : i = 1 := by rw [vs_cuts] at hi; omega
  obtain ⟨hst, hkn, hsm⟩ := vs_cut
  obtain ⟨c4, c5, c1889⟩ := vs_cells
  rw [hkn, hsm]
  refine ⟨fun m hm c hc ↦ ?_, fun _ h ↦ by simp at h⟩
  simp only [List.mem_singleton] at hm
  subst hm
  rw [hst, coreOf_19] at hl
  have ht : B1.ExpTables L.read (valG L fp (certOf 19) (.n 4)) (valG L fp (certOf 19) (.n 5)) := by
    have := hsem (6, 7) (by rw [vs_sem]; exact List.mem_singleton_self _)
    simp only [valG, c4, c5]
    exact this
  have := hvs L h16 h32 _ ht hl c hc
  simpa only [valG, Core.V.idx, c1889] using this

/-! ## `main`'s obligation -/

theorem known_main (hexp : ExpTablesSound) {κ : ℕ} {L : MemoryImage κ} {fp : K} {i : ℕ}
    (hi : i ≤ (certOf 1).cuts.length)
    (h0 : 0 < i)
    (hl : Stmt.HoldsList (coreProgram.Rel L.read) L.read (valG L fp (certOf 1))
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
  rw [main_call, holdsList_append] at hl
  have hcall := ((holdsList_noRet _ hnr _ _).mp hl).2
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hcall
  exact hexp L.read _ _ hcall.1

/-! ## The contracts -/

/-- **B2's step**: each contract for runs shorter than `n + 1`, given all of them for runs
shorter than `n`. -/
theorem b2_step (hvs : VsKnown) :
    ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ n,
      (∀ j, FunSpecLt guest L n (glob.sig j).entry (Check.Pre glob L j)
        (Check.Post coreProgram glob L certByName j)) →
      ∀ i, FunSpecLt guest L (n + 1) (glob.sig i).entry (Check.Pre glob L i)
        (Check.Post coreProgram glob L certByName i) := by
  intro κ L h16 h32 n hlt j fp k hk hpre hsafe
  obtain ⟨hgood, hjt, henv, hbnd, hmem, hsem⟩ := hpre
  have hj : 2 ≤ j ∧ j < nFns := by simpa [glob, good] using hgood
  have hc := winOk_of (j := j) (by omega) hj.2
  have h1 : (j == 1) = false := by simp; omega
  rw [h1] at hc
  have hfp := checkWin_fpOne (hc 0 (Nat.zero_le _))
  obtain ⟨hrel, hpost, hret, -⟩ := checkWins_run (Prog := coreProgram) hc (fnOf_mem hj.2)
    (coreOf_find (by omega) hj.2) (certOf_pows_ok j) h32 (fun h ↦ by rw [← hfp] at h; cases h)
    (certByName_coreOf (by omega) hj.2)
    (fun i ↦ (hlt i).mono (by omega)) hjt henv hbnd hmem hsem
    (fun i hi h0 hl ↦ by
      by_cases h19 : j = 19
      · subst h19
        exact known_vs hvs h16 h32 hsem hi h0
          (holdsList_mono (relL_le_rel _) _ id (fun _ h ↦ h) hl)
      · exact known_plain (by omega) hj.2 (by omega) h19 hi h0)
    hsafe
  obtain ⟨k', hk', r, hr, hs⟩ := hret rfl
  exact ⟨k', hk', r, hr, ⟨hrel, hpost⟩, hs⟩

/-- **B2 at `main`, located**: a halting run from `main`'s entry at `fp = 1`, the jump table
written and every contract holding for runs shorter than it, gives `main`'s body under its frame's
valuation, its calls located. -/
theorem b2_mainL (hexp : ExpTablesSound) :
    ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → JumpTables L → ∀ k,
      (∀ j, FunSpecLt guest L k (glob.sig j).entry (Check.Pre glob L j)
        (Check.Post coreProgram glob L certByName j)) →
      Safe guest L k ⟨gpow mainEntry, 1⟩ →
        Stmt.HoldsList (RL coreProgram L certByName) L.read (valG L 1 (certOf 1)) (coreOf 1).body
          False (fun rs ↦ rs = []) := by
  intro κ L _ h32 hjtab k hlt hsafe
  have hc := winOk_of (j := 1) le_rfl (by decide)
  obtain ⟨henv, hpre, hmem, hsem, hnret, hparams, hname⟩ := main_facts
  obtain ⟨-, -, -, -, -, hbody⟩ := checkWins_run (Prog := coreProgram) (fp := 1) hc
    (fnOf_mem (by decide)) (coreOf_find le_rfl (by decide)) (certOf_pows_ok 1) h32 (fun _ ↦ rfl)
    (certByName_coreOf le_rfl (by decide)) hlt
    (jtHolds_of hjtab) (by rw [Facts.entryEnv, henv]; exact EnvHolds.nil)
    (by rw [hpre]; intro _ h; simp at h) (by rw [hmem]; intro _ h; simp at h)
    (by rw [hsem]; intro _ h; simp at h)
    (fun i hi h0 hl ↦ known_main hexp hi h0 (holdsList_mono (relL_le_rel _) _ id (fun _ h ↦ h) hl))
    (by rw [fnOf_1]; exact hsafe)
  rw [hnret] at hbody
  exact hbody

end
end LeanVM.Guest.End
