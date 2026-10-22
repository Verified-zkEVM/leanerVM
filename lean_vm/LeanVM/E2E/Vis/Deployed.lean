import LeanVM.E2E.Vis.EndFinal
import LeanVM.E2E.Deployed
import Sphincs.Lifetimes

/-!
# No forgery with the visible accounting, fully instantiated (W-vis)

**Internal** (decision E2E-12): superseded as an end theorem by `LeanVM/E2E/Main.lean`, which
states the whole result. Kept as proved; its axiom pins are in `tests/LeanVMTests/E2E/Pins.lean`.

`aggregate_no_forgery_vis` at leanXMSS's proved single-key security
(`XmssSecurity.leanXmss_has_127_bits_of_classical_security`), leanSPHINCS's proved single-key
security at each proved parameter set (`Sphincs.Lifetimes.full_bits`, …), and the proved costs of
the honest signers and the final verifications. One theorem per proved set:
`aggregate_no_forgery_vis_deployed_full` (`b = 26`), `…_pruned20`, `…_pruned14`, `…_pruned13`,
`…_pruned12`, `…_pruned10`, `…_pruned8`. Their only hypotheses are the adversary's query bounds:
`qH` hash queries, `sX`/`sS` signing requests per scheme and `sXk`/`sSk` per key. The bound is
`sec0ErrorGame`, §0's bound in `Q_v = qH + budget` with the proved constants; the event is the break
at V_I's trace (`BreaksVis`), and `…_game` states today's `Breaks` in the game at the same bound.

These sit beside today's `aggregate_no_forgery_deployed_*` (`LeanVM/E2E/Deployed.lean`), for the
same event: both bounds hold, and the smaller applies (today's is smaller at one slot, the visible
one over a lifetime).

* `aggregate_no_forgery_vis_deployed_full_eps0`, `…_pruned20_eps0`: at most §0's `ε(Q_v)`
  (`eps0Game`) plus the deviations `deltaGame`.
* `aggregate_no_forgery_vis_one_slot_full`, `…_pruned20`: `n_x = n_s = 2^20`, `qH + budget ≤ 2^64`,
  `2^20` signing requests per scheme and per key: at most `2^-42 + 2^-51`.
* `aggregate_no_forgery_vis_lifetime_full`, `…_pruned20`: `n_x = n_s = 2^20`, `qH + budget ≤ 2^64`,
  `2^44` signing requests per scheme and `2^24` per key: at most `2^-41`;
  `…_lifetime_full_eps0`: at most `ε(Q_v) + 2^-84 + 2^-86 + 2^-91`.
* `aggregate_no_forgery_vis_lifetime_xmss`, `…_xmss_56`: leanXMSS keys only: at most `2^-42`
  (`Q_v ≤ 2^64`) and `2^-49` (`Q_v ≤ 2^56`).

lean_xmss's and lean_sphincs's endpoints live in non-module files, so this file is not a module.
-/

namespace LeanVM.E2E

open OracleSpec OracleComp
open scoped ENNReal

/-! ### The instantiation, generic in the parameter set -/

/-- **No forgery with the visible accounting at a parameter set**, from its single-key security
and its costs. -/
theorem aggregate_no_forgery_vis_at [Sphincs.Params] {nx ns csk css : ℕ}
    (hk : sphincsKeygenBound = csk) (hs : sphincsSignBound = css)
    (hssec : Sphincs.Security.Det.HasClassicalSecurityBitsDet 127)
    (fuel budget : ℕ) (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame nx ns 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk := by
  have hxs : xmssSignBound = 8630239197 := by rw [xmssSignBound_eq]; norm_num
  have hvx : xmssVerifyBound = 384 := by decide
  have h := aggregate_no_forgery_vis XmssSecurity.leanXmss_has_127_bits_of_classical_security hssec
    keygenFromSeed_isTotalQueryBound sphincsKeygenFromSeed_isTotalQueryBound sign_isTotalQueryBound
    sphincsSign_isTotalQueryBound verify_isTotalQueryBound sphincsVerify_isTotalQueryBound fuel
    budget A hH hX hS hXk hSk
  rwa [xmssKeygenBound_eq, hxs, hvx, hk, hs, show sphincsVerifyBound = 686 from rfl] at h

/-- **Today's event at a parameter set**, at the visible bound. -/
theorem aggregate_no_forgery_vis_game_at [Sphincs.Params] {nx ns csk css : ℕ}
    (hk : sphincsKeygenBound = csk) (hs : sphincsSignBound = css)
    (hssec : Sphincs.Security.Det.HasClassicalSecurityBitsDet 127)
    (fuel budget : ℕ) (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame nx ns 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk :=
  (prEvent_breaks_le_breaksVis Guest.guest fuel budget A).trans
    (aggregate_no_forgery_vis_at hk hs hssec fuel budget A hH hX hS hXk hSk)

/-! ### Subtree height 26 -/

section VisFull

attribute [local instance] Sphincs.Lifetimes.full

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 26**: a break
at V_I's trace has probability at most `sec0ErrorGame` with leanSPHINCS's costs
`c_sk = 15166603265`, `c_ss = 23756655991`. -/
theorem aggregate_no_forgery_vis_deployed_full {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame nx ns 13434881 15166603265 8630239197 23756655991 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_at sphincsKeygenBound_full sphincsSignBound_full
    Sphincs.Lifetimes.full_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 26**, at the visible bound. -/
theorem aggregate_no_forgery_vis_deployed_full_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame nx ns 13434881 15166603265 8630239197 23756655991 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_game_at sphincsKeygenBound_full sphincsSignBound_full
    Sphincs.Lifetimes.full_bits fuel budget A hH hX hS hXk hSk

/-- **Against §0 at subtree height 26**: at most §0's `ε(Q_v)` plus the deviations. -/
theorem aggregate_no_forgery_vis_deployed_full_eps0 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      eps0Game nx ns 13434881 15166603265 8630239197 23756655991 384 686 qH budget sX sS sXk sSk +
        deltaGame nx ns 13434881 15166603265 8630239197 23756655991 qH budget sX sS :=
  (aggregate_no_forgery_vis_deployed_full_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame_le _ _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- **One slot at subtree height 26**: `2^20` keys of each scheme, `qH + budget ≤ 2^64`, `2^20`
signing requests per scheme and per key: at most `2^-42 + 2^-51`. -/
theorem aggregate_no_forgery_vis_one_slot_full (fuel budget : ℕ)
    (A : GameAdversary (2 ^ 20) (2 ^ 20))
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk)
    (hQ : qH + budget ≤ 2 ^ 64) (hsX : sX ≤ 2 ^ 20) (hsS : sS ≤ 2 ^ 20) (hsXk : sXk ≤ 2 ^ 20)
    (hsSk : sSk ≤ 2 ^ 20) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 42 + (2 : ℝ≥0∞)⁻¹ ^ 51 :=
  (aggregate_no_forgery_vis_deployed_full_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame_one_slot (by norm_num) (by norm_num) hQ hsX hsS hsXk hsSk)

/-- **A lifetime at subtree height 26**: `2^20` keys of each scheme, `qH + budget ≤ 2^64`, `2^44`
signing requests per scheme and `2^24` per key: at most `2^-41`. -/
theorem aggregate_no_forgery_vis_lifetime_full (fuel budget : ℕ)
    (A : GameAdversary (2 ^ 20) (2 ^ 20))
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk)
    (hQ : qH + budget ≤ 2 ^ 64) (hsX : sX ≤ 2 ^ 44) (hsS : sS ≤ 2 ^ 44) (hsXk : sXk ≤ 2 ^ 24)
    (hsSk : sSk ≤ 2 ^ 24) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤ (2 : ℝ≥0∞)⁻¹ ^ 41 :=
  (aggregate_no_forgery_vis_deployed_full_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame_lifetime_le (by norm_num) (by norm_num) hQ hsX hsS hsXk hsSk)

/-- **A lifetime against §0 at subtree height 26**: at most §0's `ε(Q_v)` plus
`2^-84 + 2^-86 + 2^-91`. -/
theorem aggregate_no_forgery_vis_lifetime_full_eps0 (fuel budget : ℕ)
    (A : GameAdversary (2 ^ 20) (2 ^ 20))
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk)
    (hQ : qH + budget ≤ 2 ^ 64) (hsX : sX ≤ 2 ^ 44) (hsS : sS ≤ 2 ^ 44) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      eps0Game (2 ^ 20) (2 ^ 20) 13434881 15166603265 8630239197 23756655991 384 686 qH budget sX sS sXk sSk +
        ((2 : ℝ≥0∞)⁻¹ ^ 84 + (2 : ℝ≥0∞)⁻¹ ^ 86 + (2 : ℝ≥0∞)⁻¹ ^ 91) :=
  (aggregate_no_forgery_vis_deployed_full_eps0 fuel budget A hH hX hS hXk hSk).trans
    (add_le_add le_rfl (deltaGame_lifetime (by norm_num) (by norm_num) hQ hsX hsS))

/-- **A lifetime with leanXMSS keys only**, `Q_v ≤ 2^64`: at most `2^-42`. -/
theorem aggregate_no_forgery_vis_lifetime_xmss (fuel budget : ℕ) (A : GameAdversary (2 ^ 20) 0)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk)
    (hQ : qH + budget ≤ 2 ^ 64) (hsX : sX ≤ 2 ^ 44) (hsS : sS ≤ 2 ^ 44) (hsXk : sXk ≤ 2 ^ 24) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤ (2 : ℝ≥0∞)⁻¹ ^ 42 :=
  (aggregate_no_forgery_vis_deployed_full_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame_lifetime_xmss (by norm_num) (by norm_num) hQ hsX hsS hsXk)

/-- **A lifetime with leanXMSS keys only**, `Q_v ≤ 2^56`: at most `2^-49`. -/
theorem aggregate_no_forgery_vis_lifetime_xmss_56 (fuel budget : ℕ) (A : GameAdversary (2 ^ 20) 0)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk)
    (hQ : qH + budget ≤ 2 ^ 56) (hsX : sX ≤ 2 ^ 44) (hsS : sS ≤ 2 ^ 44) (hsXk : sXk ≤ 2 ^ 24) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤ (2 : ℝ≥0∞)⁻¹ ^ 49 :=
  (aggregate_no_forgery_vis_deployed_full_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame_lifetime_xmss_56 (by norm_num) (by norm_num) hQ hsX hsS hsXk)

end VisFull

/-! ### Subtree height 20 -/

section VisPruned20

attribute [local instance] Sphincs.Lifetimes.pruned20

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 20**: a break
at V_I's trace has probability at most `sec0ErrorGame` with leanSPHINCS's costs
`c_sk = 236978189`, `c_ss = 8827030915`. -/
theorem aggregate_no_forgery_vis_deployed_pruned20 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame nx ns 13434881 236978189 8630239197 8827030915 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_at sphincsKeygenBound_pruned20 sphincsSignBound_pruned20
    Sphincs.Lifetimes.pruned20_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 20**, at the visible bound. -/
theorem aggregate_no_forgery_vis_deployed_pruned20_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame nx ns 13434881 236978189 8630239197 8827030915 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_game_at sphincsKeygenBound_pruned20 sphincsSignBound_pruned20
    Sphincs.Lifetimes.pruned20_bits fuel budget A hH hX hS hXk hSk

/-- **Against §0 at subtree height 20**: at most §0's `ε(Q_v)` plus the deviations. -/
theorem aggregate_no_forgery_vis_deployed_pruned20_eps0 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      eps0Game nx ns 13434881 236978189 8630239197 8827030915 384 686 qH budget sX sS sXk sSk +
        deltaGame nx ns 13434881 236978189 8630239197 8827030915 qH budget sX sS :=
  (aggregate_no_forgery_vis_deployed_pruned20_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame_le _ _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- **One slot at subtree height 20**: `2^20` keys of each scheme, `qH + budget ≤ 2^64`, `2^20`
signing requests per scheme and per key: at most `2^-42 + 2^-51`. -/
theorem aggregate_no_forgery_vis_one_slot_pruned20 (fuel budget : ℕ)
    (A : GameAdversary (2 ^ 20) (2 ^ 20))
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk)
    (hQ : qH + budget ≤ 2 ^ 64) (hsX : sX ≤ 2 ^ 20) (hsS : sS ≤ 2 ^ 20) (hsXk : sXk ≤ 2 ^ 20)
    (hsSk : sSk ≤ 2 ^ 20) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 42 + (2 : ℝ≥0∞)⁻¹ ^ 51 :=
  (aggregate_no_forgery_vis_deployed_pruned20_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame_one_slot (by norm_num) (by norm_num) hQ hsX hsS hsXk hsSk)

/-- **A lifetime at subtree height 20**: `2^20` keys of each scheme, `qH + budget ≤ 2^64`, `2^44`
signing requests per scheme and `2^24` per key: at most `2^-41`. -/
theorem aggregate_no_forgery_vis_lifetime_pruned20 (fuel budget : ℕ)
    (A : GameAdversary (2 ^ 20) (2 ^ 20))
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk)
    (hQ : qH + budget ≤ 2 ^ 64) (hsX : sX ≤ 2 ^ 44) (hsS : sS ≤ 2 ^ 44) (hsXk : sXk ≤ 2 ^ 24)
    (hsSk : sSk ≤ 2 ^ 24) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤ (2 : ℝ≥0∞)⁻¹ ^ 41 :=
  (aggregate_no_forgery_vis_deployed_pruned20_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame_lifetime_le (by norm_num) (by norm_num) hQ hsX hsS hsXk hsSk)

end VisPruned20

/-! ### Subtree height 14 -/

section VisPruned14

attribute [local instance] Sphincs.Lifetimes.pruned14

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 14**: a break
at V_I's trace has probability at most `sec0ErrorGame` with leanSPHINCS's costs
`c_sk = 3702809`, `c_ss = 8593755535`. -/
theorem aggregate_no_forgery_vis_deployed_pruned14 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame nx ns 13434881 3702809 8630239197 8593755535 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 3702556 by decide])
    Sphincs.Lifetimes.pruned14_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 14**, at the visible bound. -/
theorem aggregate_no_forgery_vis_deployed_pruned14_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame nx ns 13434881 3702809 8630239197 8593755535 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_game_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 3702556 by decide])
    Sphincs.Lifetimes.pruned14_bits fuel budget A hH hX hS hXk hSk

end VisPruned14

/-! ### Subtree height 13 -/

section VisPruned13

attribute [local instance] Sphincs.Lifetimes.pruned13

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 13**: a break
at V_I's trace has probability at most `sec0ErrorGame` with leanSPHINCS's costs
`c_sk = 1851419`, `c_ss = 8591904145`. -/
theorem aggregate_no_forgery_vis_deployed_pruned13 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame nx ns 13434881 1851419 8630239197 8591904145 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 1851166 by decide])
    Sphincs.Lifetimes.pruned13_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 13**, at the visible bound. -/
theorem aggregate_no_forgery_vis_deployed_pruned13_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame nx ns 13434881 1851419 8630239197 8591904145 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_game_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 1851166 by decide])
    Sphincs.Lifetimes.pruned13_bits fuel budget A hH hX hS hXk hSk

end VisPruned13

/-! ### Subtree height 12 -/

section VisPruned12

attribute [local instance] Sphincs.Lifetimes.pruned12

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 12**: a break
at V_I's trace has probability at most `sec0ErrorGame` with leanSPHINCS's costs
`c_sk = 925725`, `c_ss = 8590978451`. -/
theorem aggregate_no_forgery_vis_deployed_pruned12 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame nx ns 13434881 925725 8630239197 8590978451 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 925472 by decide])
    Sphincs.Lifetimes.pruned12_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 12**, at the visible bound. -/
theorem aggregate_no_forgery_vis_deployed_pruned12_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame nx ns 13434881 925725 8630239197 8590978451 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_game_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 925472 by decide])
    Sphincs.Lifetimes.pruned12_bits fuel budget A hH hX hS hXk hSk

end VisPruned12

/-! ### Subtree height 10 -/

section VisPruned10

attribute [local instance] Sphincs.Lifetimes.pruned10

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 10**: a break
at V_I's trace has probability at most `sec0ErrorGame` with leanSPHINCS's costs
`c_sk = 231457`, `c_ss = 8590284183`. -/
theorem aggregate_no_forgery_vis_deployed_pruned10 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame nx ns 13434881 231457 8630239197 8590284183 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 231204 by decide])
    Sphincs.Lifetimes.pruned10_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 10**, at the visible bound. -/
theorem aggregate_no_forgery_vis_deployed_pruned10_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame nx ns 13434881 231457 8630239197 8590284183 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_game_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 231204 by decide])
    Sphincs.Lifetimes.pruned10_bits fuel budget A hH hX hS hXk hSk

end VisPruned10

/-! ### Subtree height 8 -/

section VisPruned8

attribute [local instance] Sphincs.Lifetimes.pruned8

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 8**: a break
at V_I's trace has probability at most `sec0ErrorGame` with leanSPHINCS's costs
`c_sk = 57893`, `c_ss = 8590110619`. -/
theorem aggregate_no_forgery_vis_deployed_pruned8 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame nx ns 13434881 57893 8630239197 8590110619 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 57640 by decide])
    Sphincs.Lifetimes.pruned8_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 8**, at the visible bound. -/
theorem aggregate_no_forgery_vis_deployed_pruned8_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame nx ns 13434881 57893 8630239197 8590110619 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis_game_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 57640 by decide])
    Sphincs.Lifetimes.pruned8_bits fuel budget A hH hX hS hXk hSk

end VisPruned8

end LeanVM.E2E
