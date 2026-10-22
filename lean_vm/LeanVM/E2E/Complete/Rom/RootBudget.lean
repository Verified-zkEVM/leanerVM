/-
  LeanVM.E2E.Complete.Rom.RootBudget

  T6-prob's two-level inhabitant: the deployed budget at the work of a node with one child and one
  leanXMSS claim held through it.
-/

module

public import LeanVM.E2E.Complete.Rom.RootBudgetF

/-!
# The budget at a node with one child

The work of a root holding one leanXMSS claim through its one child is `⟨1, 1, 0, 0, 0, 0, 1, 1⟩`
(one declared claim, one coverage slot, one child making one claim, `rootWork`). Its committed
size under the deployed budget is below `2^28` (`budget_rootWork`): at most `2^21` words, at most
`2^20` instructions of each opcode but `BLAKE2S`'s `2^17`.

The words at a child include `open_stacked`'s bound `Bop`, the largest of its 28 configurations'
(`osBop`). The kernel cannot evaluate the words in one piece (it reduces `Bop` along, beyond
30 GB), so they are split, over variables, as the rest at `Bop = 0` plus `Bop`
(`eaLin_eval_vs_split`); the rest is evaluated (`rootWords_rest_le`) and `Bop` is bounded
configuration by configuration (`RootBudgetA.lean`, `RootBudgetB.lean`, `bop_le_rb`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B2C

@[expose] public section

/-- **`open_stacked`'s bound is within `2^20` words.** -/
theorem bop_le_rb : calleesHyps_b2c.Bop ≤ 2 ^ 20 := by
  show osBop fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) ≤ 2 ^ 20
  unfold osBop
  exact
    max_le osCfgBound_le_rb0 <|
    max_le osCfgBound_le_rb1 <|
    max_le osCfgBound_le_rb2 <|
    max_le osCfgBound_le_rb3 <|
    max_le osCfgBound_le_rb4 <|
    max_le osCfgBound_le_rb5 <|
    max_le osCfgBound_le_rb6 <|
    max_le osCfgBound_le_rb7 <|
    max_le osCfgBound_le_rb8 <|
    max_le osCfgBound_le_rb9 <|
    max_le osCfgBound_le_rb10 <|
    max_le osCfgBound_le_rb11 <|
    max_le osCfgBound_le_rb12 <|
    max_le osCfgBound_le_rb13 <|
    max_le osCfgBound_le_rb14 <|
    max_le osCfgBound_le_rb15 <|
    max_le osCfgBound_le_rb16 <|
    max_le osCfgBound_le_rb17 <|
    max_le osCfgBound_le_rb18 <|
    max_le osCfgBound_le_rb19 <|
    max_le osCfgBound_le_rb20 <|
    max_le osCfgBound_le_rb21 <|
    max_le osCfgBound_le_rb22 <|
    max_le osCfgBound_le_rb23 <|
    max_le osCfgBound_le_rb24 <|
    max_le osCfgBound_le_rb25 <|
    max_le osCfgBound_le_rb26 <|
    osCfgBound_le_rb27

/-! ## The words -/

/-- **The words at a work, split at `verify_sub`'s `open_stacked` bound**, over variables. -/
theorem eaLin_eval_vs_split (fr : String → ℕ) (Bd : Main.CalleeBounds) (A : Main.EaAffC)
    (Bs : VerifySub.VsBounds) (u : End.Work) (Bd' : Main.CalleeBounds)
    (hvs : Bd.vs = VerifySub.vsBound fr Bs)
    (h' : Bd' = { Bd with vs := VerifySub.vsBound fr { Bs with op := 0 } }) :
    (Main.eaLin fr Bd A).eval u = (Main.eaLin fr Bd' A).eval u + Bs.op * u.children := by
  subst h'
  obtain ⟨_, _, _, _, _, _, _, _, _, vs, _⟩ := Bd
  simp only at hvs
  subst hvs
  simp only [Main.eaLin, End.Linear.eval, Main.eaChK, Main.eaChA, VerifySub.vsBound,
    VerifySub.vsKidsBound]
  ring

/-- **The words at the root's work are within `2^21`.** -/
theorem rootWords_le : (b2cBudget'.words).eval rootWork ≤ 2 ^ 21 := by
  have h := eaLin_eval_vs_split fs (Main.calleeBd fs calleesHyps_b2c)
    (Main.eaWordsC fs calleesHyps_b2c 482 0) (Main.calleeVsB fs calleesHyps_b2c) rootWork rootBdRest
    rfl rfl
  have hop : (Main.calleeVsB fs calleesHyps_b2c).op = calleesHyps_b2c.Bop := rfl
  rw [hop] at h
  have hw : (b2cBudget'.words).eval rootWork =
      (Main.eaLin fs (Main.calleeBd fs calleesHyps_b2c)
        (Main.eaWordsC fs calleesHyps_b2c 482 0)).eval rootWork := by
    simp only [b2cBudget', b2cBudget, Main.eaBudget, Main.eaWords]
  have hr := rootWords_rest_le
  have hb := bop_le_rb
  have hc : rootWork.children = 1 := rfl
  rw [hw, h, hc, Nat.mul_one]
  generalize (Main.eaLin fs rootBdRest (Main.eaWordsC fs calleesHyps_b2c 482 0)).eval rootWork = a
    at hr ⊢
  generalize calleesHyps_b2c.Bop = b at hb ⊢
  omega

/-! ## The instructions -/

theorem rootInstrs_le (op : Opcode) :
    (b2cBudget'.instrs op).eval rootWork ≤ rootInstrsBound op := by
  cases op
  · exact rootInstrs_xor
  · exact rootInstrs_mulNative
  · exact rootInstrs_setConstant
  · exact rootInstrs_deref
  · exact rootInstrs_jump
  · exact rootInstrs_blake2s

/-- **The root's committed size is within the deployed budget.** -/
theorem budget_rootWork : b2cBudget'.size rootWork ≤ 2 ^ 28 := by
  refine (End.sizeOf_mono rootWords_le rootInstrs_le).trans ?_
  simp only [End.sizeOf, rootInstrsBound, Memory.logMem, Nat.clog_pow 2 _ one_lt_two,
    guest_logSize, minLogMem]
  norm_num

end
end LeanVM.E2E.Complete
