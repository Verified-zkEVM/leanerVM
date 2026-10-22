/-
  LeanVM.E2E.Vis.EndFinal2

  W-vis, the end theorem with T3 from two challenges: a break at V_I's trace has probability at
  most `sec0ErrorGame2`, whose T3 term is `Q_v³ / (6 · 2^384)`.
-/

module

public import LeanVM.E2E.Vis.EndFinal
public import LeanVM.E2E.Vis.Closed2

/-!
# No forgery with the visible accounting, T3 from two challenges

The assembly of `Vis/PerKey/Sum.lean`, `Vis/NoForgery.lean`, `Vis/End.lean` and
`Vis/EndFinal.lean`, with the bad events `AggBadV2` (`Vis/Bound2.lean`) for `AggBadV`: T4 at the
trace takes `RankOK2` (`rankOK2_of_not_aggBadV2`), the per-key hybrid is unchanged, and the
chain's error is `visError2`.

* `aggregate_no_forgery_vis2`: a break at V_I's trace (`BreaksVis`) has probability at most
  `sec0ErrorGame2`, under `aggregate_no_forgery_vis`'s hypotheses.
* `aggregate_no_forgery_vis2_game`: today's event `Breaks` in the game, at the same bound.

`sec0ErrorGame2` is `sec0ErrorGame` with `Q_v³ / (6 · 2^384)` for `Q_v (Q_v + 1) / 2^193`
(`sec0Error2_add`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ} [Sphincs.Params]

/-- **A leanXMSS forgery on a good log is a win of reduction `j`.** -/
theorem xWinAt_of_gameRec2
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {p : (GameOutcome nx ns × Log) × Log}
    (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (ha : p.1.1.accepted = true)
    (hbad : ¬ AggBadV2 p.1.1.keys p.2) {j : Fin nx} (hf : ForgedXAt j p.1.1) :
    XWinAt j p.1.1 p.1.2 := by
  have hk := gameRec_knows hG hp ha (not_aggBadT_of_not_aggBadV2 hbad)
    (rankOK2_of_not_aggBadV2 hbad)
  obtain ⟨msg, hmem, hfr⟩ := hf
  obtain ⟨σ, hσ⟩ := hk.1 _ hmem
  exact ⟨ha, msg, σ, hmem, hfr, hσ⟩

/-- **A leanSPHINCS forgery on a good log is a win of reduction `j`.** -/
theorem sWinAt_of_gameRec2
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {p : (GameOutcome nx ns × Log) × Log}
    (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (ha : p.1.1.accepted = true)
    (hbad : ¬ AggBadV2 p.1.1.keys p.2) {j : Fin ns} (hf : ForgedSAt j p.1.1) :
    SWinAt j p.1.1 p.1.2 := by
  have hk := gameRec_knows hG hp ha (not_aggBadT_of_not_aggBadV2 hbad)
    (rankOK2_of_not_aggBadV2 hbad)
  obtain ⟨msg, hmem, hfr⟩ := hf
  obtain ⟨σ, hσ⟩ := hk.2.1 _ hmem
  exact ⟨ha, msg, σ, hmem, hfr, hσ⟩


/-- **The hybrid over keys (P7c).** In the game with V_I's trace, V_I accepting a forgery on a log
without the chain's bad events is at most as likely as, summed over the keys, reduction `j`'s
win without a coincidence at key `j`, plus that coincidence. -/
theorem prEvent_forged_le_perKey2
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (fuel budget : ℕ) (A : GameAdversary nx ns) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[p.1.1.accepted = true ∧ Forged p.1.1 ∧
        ¬ AggBadV2 p.1.1.keys p.2] ≤
      ∑ j : Fin nx, (Pr{let p ← gameRec Guest.guest fuel budget A}[XWinAt j p.1.1 p.1.2 ∧
          ¬ KeyCollAt p.1.1.keys (Fin.castAdd ns j)] +
        Pr{let p ← gameRec Guest.guest fuel budget A}[KeyCollAt p.1.1.keys (Fin.castAdd ns j)]) +
      ∑ j : Fin ns, (Pr{let p ← gameRec Guest.guest fuel budget A}[SWinAt j p.1.1 p.1.2 ∧
          ¬ KeyCollAt p.1.1.keys (Fin.natAdd nx j)] +
        Pr{let p ← gameRec Guest.guest fuel budget A}[KeyCollAt p.1.1.keys (Fin.natAdd nx j)]) := by
  calc Pr{let p ← gameRec Guest.guest fuel budget A}[p.1.1.accepted = true ∧ Forged p.1.1 ∧
        ¬ AggBadV2 p.1.1.keys p.2]
      ≤ Pr{let p ← gameRec Guest.guest fuel budget A}[(∃ j, XWinAt j p.1.1 p.1.2) ∨
          ∃ j, SWinAt j p.1.1 p.1.2] := by
        refine prEvent_mono_of_support _ _ _ fun p hp h ↦ ?_
        rcases (forged_iff_exists p.1.1).mp h.2.1 with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact Or.inl ⟨j, xWinAt_of_gameRec2 hG hp h.1 h.2.2 hj⟩
        · exact Or.inr ⟨j, sWinAt_of_gameRec2 hG hp h.1 h.2.2 hj⟩
    _ ≤ ∑ j, Pr{let p ← gameRec Guest.guest fuel budget A}[XWinAt j p.1.1 p.1.2] +
          ∑ j, Pr{let p ← gameRec Guest.guest fuel budget A}[SWinAt j p.1.1 p.1.2] :=
        prEvent_or_exists_le_sum _ _ _
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun j _ ↦ prEvent_le_and_not_add _ _ _)
        (Finset.sum_le_sum fun j _ ↦ prEvent_le_and_not_add _ _ _)


/-- **On a good log, a break at the trace is a forgery**: the trace backs every DA claim. -/
theorem forged_of_breaksVis2
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {p : (GameOutcome nx ns × Log) × Log}
    (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (hb : BreaksVis p.1.1 p.1.2)
    (hbad : ¬ AggBadV2 p.1.1.keys p.2) : Forged p.1.1 := by
  rcases hb.2 with hf | ⟨c, hc, hn⟩
  · exact hf
  · have hk := gameRec_knows hG hp hb.1 (not_aggBadT_of_not_aggBadV2 hbad)
      (rankOK2_of_not_aggBadV2 hbad)
    exact absurd (hk.2.2 c hc) hn

/-- **The break, from the bad events and the per-key hybrid.** In the game with V_I's trace, if
reduction `j`'s win without a coincidence at key `j` has probability at most `ax` (leanXMSS) or
`as` (leanSPHINCS), and each key's coincidence at most `k`, a break at the trace has probability
at most the bad events' plus `n_x (ax + k) + n_s (as + k)`. -/
theorem prEvent_breaksVis_le_of2
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (fuel budget : ℕ) (A : GameAdversary nx ns) {ax as k : ℝ≥0∞}
    (hx : ∀ j : Fin nx, Pr{let p ← gameRec Guest.guest fuel budget A}[XWinAt j p.1.1 p.1.2 ∧
      ¬ KeyCollAt p.1.1.keys (Fin.castAdd ns j)] ≤ ax)
    (hs : ∀ j : Fin ns, Pr{let p ← gameRec Guest.guest fuel budget A}[SWinAt j p.1.1 p.1.2 ∧
      ¬ KeyCollAt p.1.1.keys (Fin.natAdd nx j)] ≤ as)
    (hk : ∀ idx, Pr{let p ← gameRec Guest.guest fuel budget A}[KeyCollAt p.1.1.keys idx] ≤ k) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      Pr{let p ← gameRec Guest.guest fuel budget A}[AggBadV2 p.1.1.keys p.2] +
        (nx * (ax + k) + ns * (as + k)) := by
  calc Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2]
      ≤ Pr{let p ← gameRec Guest.guest fuel budget A}[AggBadV2 p.1.1.keys p.2 ∨
          (p.1.1.accepted = true ∧ Forged p.1.1 ∧ ¬ AggBadV2 p.1.1.keys p.2)] := by
        refine prEvent_mono_of_support _ _ _ fun p hp h ↦ ?_
        by_cases hbad : AggBadV2 p.1.1.keys p.2
        · exact Or.inl hbad
        · exact Or.inr ⟨h.1, forged_of_breaksVis2 hG hp h hbad, hbad⟩
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := by
        refine add_le_add le_rfl ((prEvent_forged_le_perKey2 hG fuel budget A).trans ?_)
        refine add_le_add ?_ ?_
        · refine (Finset.sum_le_sum fun j _ ↦ add_le_add (hx j) (hk _)).trans ?_
          simp [mul_add]
        · refine (Finset.sum_le_sum fun j _ ↦ add_le_add (hs j) (hk _)).trans ?_
          simp [mul_add]


/-- **The end theorem's assembly.** For the game of the deployed guest: if leanXMSS and
leanSPHINCS have 127 bits of single-key security, the honest costs are bounded, each per-key
reduction makes at most `Q_v + q_x` (resp. `Q_v + q_s`) hash calls, and leanSPHINCS reduction
`j`'s win bounds the game's win against key `j` without a coincidence, then a break at V_I's trace
has probability at most `sec0ErrorGame2`, T3 from two challenges. -/
theorem prEvent_breaksVis_le_sec0_2
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
      sec0ErrorGame2 nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk := by
  have hn : ∀ (j : Fin (nx + ns)) (c : ℕ), 2 * (nx + ns) ≤ c → 1 ≤ qH + budget + c :=
    fun j c hc ↦ by have := j.pos; omega
  refine (prEvent_breaksVis_le_of2 hG fuel budget A
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
  · rw [sec0ErrorGame2, sec0Error2, perKeyError, perKey_regroup]
    exact add_le_add (prEvent_gameRec_aggBadV2_le hxk hsk hxs hss fuel budget A hH hX hS) le_rfl


/-- **No forgery with the visible accounting (the end theorem).** For the game of the deployed
guest with `n_x` leanXMSS and `n_s` leanSPHINCS honest keys and an adversary making at most `qH`
hash queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests, at most `sXk` (`sSk`) to each
leanXMSS (leanSPHINCS) key: if leanXMSS and leanSPHINCS have 127 bits of single-key security and
the honest key generations, signatures and verifications make at most `cxk`, `csk`, `cxs`, `css`,
`cx`, `cs` hash queries, then V_I accepting a root statement with a forged claim of an honest key
or a DA claim its own trace does not back has probability at most `sec0ErrorGame2`: §0's bound,
with `Q_v = qH + budget` visible queries, with the constants the proofs give. -/
theorem aggregate_no_forgery_vis2
    (hxsec : LeanXmss.LeanXmssSecurityStatement)
    (hssec : Sphincs.Security.Det.HasClassicalSecurityBitsDet 127)
    {cxk csk cxs css cx cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvx : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame2 nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk :=
  prEvent_breaksVis_le_sec0_2 (fun _ _ _ ↦ guestHypsM_model _) hxsec hssec hxk hsk hxs hss fuel
    budget A hH hX hS
    (fun j r hr ↦ (PerKeyX.hasHashQueryBound_xRedJ hxk hxs hvx Guest.guest fuel budget A j hH
      (hXk j) r hr).trans (by omega))
    (fun j ↦ ⟨_, fun r hr ↦ (PerKeyS.hasHashQueryBound_sRedJ hsk hss hvs Guest.guest fuel budget
      A j hH (hSk j) r hr).trans (by omega), PerKeyS.prEvent_sWinAt_le Guest.guest fuel budget A j⟩)

/-- **Today's event at the visible bound**: a break against the oracle's final log in the game. -/
theorem aggregate_no_forgery_vis2_game
    (hxsec : LeanXmss.LeanXmssSecurityStatement)
    (hssec : Sphincs.Security.Det.HasClassicalSecurityBitsDet 127)
    {cxk csk cxs css cx cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvx : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame2 nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk :=
  (prEvent_breaks_le_breaksVis Guest.guest fuel budget A).trans
    (aggregate_no_forgery_vis2 hxsec hssec hxk hsk hxs hss hvx hvs fuel budget A hH hX hS hXk hSk)

end

end LeanVM.E2E
