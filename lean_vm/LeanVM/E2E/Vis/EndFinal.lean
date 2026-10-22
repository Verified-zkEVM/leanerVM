/-
  LeanVM.E2E.Vis.EndFinal

  W-vis, the end theorem: no forgery with the visible accounting, bounded by `sec0ErrorGame`, and
  by §0's `ε(Q_v)` plus the explicit deviations.
-/

module

public import LeanVM.E2E.Vis.End
public import LeanVM.E2E.Vis.PerKey.XmssCount
public import LeanVM.E2E.Vis.PerKey.SphincsCount
public import LeanVM.E2E.Guest

/-!
# No forgery with the visible accounting (W-vis, the end theorem)

**Internal** (decision E2E-12): superseded as an end theorem by `LeanVM/E2E/Main.lean`, which
states the whole result. Kept as proved; its axiom pins are in `tests/LeanVMTests/E2E/Pins.lean`.

* `aggregate_no_forgery_vis`: for the game of the deployed guest, a break at V_I's trace
  (`BreaksVis`) has probability at most `sec0ErrorGame`. The hypotheses are 127 bits of single-key
  security for leanXMSS and leanSPHINCS, the honest costs, and the adversary's query bounds:
  `qH` hash queries, `sX`/`sS` signing requests per scheme, and `sXk`/`sSk` per key.
* `aggregate_no_forgery_vis_eps0`: the same, at most §0's `ε(Q_v)` (`eps0Game`) plus the
  deviations `deltaGame` (E2E-6, E2E-7, `Vis/Closed.lean`).
* `aggregate_no_forgery_vis_game`, `aggregate_no_forgery_vis_game_eps0`: today's event `Breaks`
  in the game, at the same bounds (`prEvent_breaks_le_breaksVis`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ} [Sphincs.Params]

/-- **No forgery with the visible accounting (the end theorem).** For the game of the deployed
guest with `n_x` leanXMSS and `n_s` leanSPHINCS honest keys and an adversary making at most `qH`
hash queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests, at most `sXk` (`sSk`) to each
leanXMSS (leanSPHINCS) key: if leanXMSS and leanSPHINCS have 127 bits of single-key security and
the honest key generations, signatures and verifications make at most `cxk`, `csk`, `cxs`, `css`,
`cx`, `cs` hash queries, then V_I accepting a root statement with a forged claim of an honest key
or a DA claim its own trace does not back has probability at most `sec0ErrorGame`: §0's bound,
with `Q_v = qH + budget` visible queries, with the constants the proofs give. -/
theorem aggregate_no_forgery_vis
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
      sec0ErrorGame nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk :=
  prEvent_breaksVis_le_sec0 (fun _ _ _ ↦ guestHypsM_model _) hxsec hssec hxk hsk hxs hss fuel
    budget A hH hX hS
    (fun j r hr ↦ (PerKeyX.hasHashQueryBound_xRedJ hxk hxs hvx Guest.guest fuel budget A j hH
      (hXk j) r hr).trans (by omega))
    (fun j ↦ ⟨_, fun r hr ↦ (PerKeyS.hasHashQueryBound_sRedJ hsk hss hvs Guest.guest fuel budget
      A j hH (hSk j) r hr).trans (by omega), PerKeyS.prEvent_sWinAt_le Guest.guest fuel budget A j⟩)

/-- **The end theorem against §0**: at most §0's `ε(Q_v)` (`eps0Game`) plus the deviations
`deltaGame`. -/
theorem aggregate_no_forgery_vis_eps0
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
      eps0Game nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk +
        deltaGame nx ns cxk csk cxs css qH budget sX sS :=
  (aggregate_no_forgery_vis hxsec hssec hxk hsk hxs hss hvx hvs fuel budget A hH hX hS hXk
    hSk).trans (sec0ErrorGame_le _ _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- **Today's event at the visible bound**: a break against the oracle's final log in the game. -/
theorem aggregate_no_forgery_vis_game
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
      sec0ErrorGame nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk :=
  (prEvent_breaks_le_breaksVis Guest.guest fuel budget A).trans
    (aggregate_no_forgery_vis hxsec hssec hxk hsk hxs hss hvx hvs fuel budget A hH hX hS hXk hSk)

/-- **Today's event against §0.** -/
theorem aggregate_no_forgery_vis_game_eps0
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
      eps0Game nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk +
        deltaGame nx ns cxk csk cxs css qH budget sX sS :=
  (aggregate_no_forgery_vis_game hxsec hssec hxk hsk hxs hss hvx hvs fuel budget A hH hX hS hXk
    hSk).trans (sec0ErrorGame_le _ _ _ _ _ _ _ _ _ _ _ _ _ _)

end

end LeanVM.E2E
