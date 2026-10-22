/-
  LeanVM.E2E.Vis.End

  W-vis, P6: the end theorem's assembly. The break at V_I's trace is bounded by `sec0Error`: the
  chain's bad events (`visError`, P6a), and per key the single-key theorem at the reduction's
  count and the key coincidence (P7d).
-/

module

public import LeanVM.E2E.Vis.NoForgery
public import LeanVM.E2E.Vis.Closed
public import LeanVM.E2E.Vis.PerKey.Coll
public import LeanVM.E2E.Vis.PerKey.XmssChain
public import Sphincs.StatementDet

/-!
# The end theorem's assembly (W-vis, P6)

* `prEvent_breaksVis_le_sec0`: the break at V_I's trace is at most `sec0ErrorGame`, from the
  schemes' single-key security, each reduction's hash-call count, and leanSPHINCS's per-key
  bound (`hsw`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ} [Sphincs.Params]

omit [Sphincs.Params] in
/-- `q / 2^127`, the cast's two forms. -/
theorem div_two_pow_127_cast (q : ℕ) :
    (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) = (q : ℝ≥0∞) / 2 ^ 127 := by
  rw [Nat.cast_pow, Nat.cast_ofNat]

omit [Sphincs.Params] in
/-- The per-key sum, regrouped. -/
theorem perKey_regroup (a b c d k : ℝ≥0∞) :
    a * (c + k) + b * (d + k) = a * c + b * d + (a + b) * k := by ring

/-- **The end theorem's assembly.** For the game of the deployed guest: if leanXMSS and
leanSPHINCS have 127 bits of single-key security, the honest costs are bounded, each per-key
reduction makes at most `Q_v + q_x` (resp. `Q_v + q_s`) hash calls, and leanSPHINCS reduction
`j`'s win bounds the game's win against key `j` without a coincidence, then a break at V_I's trace
has probability at most `sec0ErrorGame`. -/
theorem prEvent_breaksVis_le_sec0
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hxsec : LeanXmss.LeanXmssSecurityStatement)
    (hssec : Sphincs.Security.Det.HasClassicalSecurityBitsDet 127)
    {cxk csk cxs css cx cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hcx : ∀ j : Fin nx, LeanXmss.Security.HasHashQueryBound
      (PerKeyX.xRedJ Guest.guest fuel budget A j)
      (qH + budget + (2 * (nx + ns) + cxk + sXk * cxs + cx)))
    (hsw : ∀ j : Fin ns, ∃ adv : Sphincs.Security.Adversary,
      Sphincs.Security.Det.HasHashQueryBoundDet adv
        (qH + budget + (2 * (nx + ns) + csk + sSk * css + cs)) ∧
      Pr{let p ← gameRec Guest.guest fuel budget A}[SWinAt j p.1.1 p.1.2 ∧
        ¬ KeyCollAt p.1.1.keys (Fin.natAdd nx j)] ≤ Sphincs.Security.Det.forgeAdvantageDet adv) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk := by
  have hn : ∀ (j : Fin (nx + ns)) (c : ℕ), 2 * (nx + ns) ≤ c → 1 ≤ qH + budget + c :=
    fun j c hc ↦ by have := j.pos; omega
  refine (prEvent_breaksVis_le_of hG fuel budget A
    (ax := ((qH + budget + (2 * (nx + ns) + cxk + sXk * cxs + cx) : ℕ) : ℝ≥0∞) / 2 ^ 127)
    (as := ((qH + budget + (2 * (nx + ns) + csk + sSk * css + cs) : ℕ) : ℝ≥0∞) / 2 ^ 127)
    (k := ((2 * (nx + ns) : ℕ) : ℝ≥0∞) / 2 ^ 128 + ((nx * cxk + ns * csk) ^ 2 : ℕ) / 2 ^ 256)
    (fun j ↦ ?_) (fun j ↦ ?_) (fun idx ↦ prEvent_gameRec_keyCollAt_le idx _ fuel budget A hxk hsk)).trans
    ?_
  · refine (PerKeyX.prEvent_xWinAt_le Guest.guest fuel budget A j).trans ?_
    have h := hxsec _ (hn (Fin.castAdd ns j) _ (by omega)) _ (hcx j)
    rwa [div_two_pow_127_cast] at h
  · obtain ⟨adv, hq, hw⟩ := hsw j
    have h := hssec _ (hn (Fin.natAdd nx j) _ (by omega)) _ hq
    rw [div_two_pow_127_cast] at h
    exact hw.trans h
  · rw [sec0ErrorGame, sec0Error, perKeyError, perKey_regroup]
    exact add_le_add (prEvent_gameRec_aggBadV_le hxk hsk hxs hss fuel budget A hH hX hS) le_rfl

end

end LeanVM.E2E
