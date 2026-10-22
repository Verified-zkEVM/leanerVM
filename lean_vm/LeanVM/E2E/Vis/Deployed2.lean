import LeanVM.E2E.Vis.EndFinal2
import LeanVM.E2E.Deployed
import Sphincs.Lifetimes

/-!
# No forgery with the visible accounting, T3 from two challenges, fully instantiated (W-vis)

`Vis/Deployed.lean` with `aggregate_no_forgery_vis2` (`Vis/EndFinal2.lean`) for
`aggregate_no_forgery_vis`: the bound is `sec0ErrorGame2`, whose T3 term is
`Q_v³ / (6 · 2^384)` for `Q_v (Q_v + 1) / 2^193`. One theorem per proved leanSPHINCS set:
`aggregate_no_forgery_vis2_deployed_full` (`b = 26`), `…_pruned20`, `…_pruned14`, `…_pruned13`,
`…_pruned12`, `…_pruned10`, `…_pruned8`, each with its `…_game` form for today's `Breaks`.

* `aggregate_no_forgery_vis2_one_slot_full`, `…_pruned20`: at most `2^-42 + 2^-51`.
* `aggregate_no_forgery_vis2_lifetime_full`, `…_pruned20`: at most `2^-41`.
* `aggregate_no_forgery_vis2_lifetime_xmss`, `…_xmss_56`: at most `2^-42` and `2^-49`.

`Vis/Deployed.lean`'s `…_eps0` forms compare with §0's literal `ε(Q_v)`, whose T3 term is the
birthday bound; they are not restated here.

lean_xmss's and lean_sphincs's endpoints live in non-module files, so this file is not a module.
-/

namespace LeanVM.E2E

open OracleSpec OracleComp
open scoped ENNReal

/-! ### The instantiation, generic in the parameter set -/

/-- **No forgery with the visible accounting at a parameter set**, from its single-key security
and its costs. -/
theorem aggregate_no_forgery_vis2_at [Sphincs.Params] {nx ns csk css : ℕ}
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
      sec0ErrorGame2 nx ns 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk := by
  have hxs : xmssSignBound = 8630239197 := by rw [xmssSignBound_eq]; norm_num
  have hvx : xmssVerifyBound = 384 := by decide
  have h := aggregate_no_forgery_vis2 XmssSecurity.leanXmss_has_127_bits_of_classical_security hssec
    keygenFromSeed_isTotalQueryBound sphincsKeygenFromSeed_isTotalQueryBound sign_isTotalQueryBound
    sphincsSign_isTotalQueryBound verify_isTotalQueryBound sphincsVerify_isTotalQueryBound fuel
    budget A hH hX hS hXk hSk
  rwa [xmssKeygenBound_eq, hxs, hvx, hk, hs, show sphincsVerifyBound = 686 from rfl] at h

/-- **Today's event at a parameter set**, at the visible bound. -/
theorem aggregate_no_forgery_vis2_game_at [Sphincs.Params] {nx ns csk css : ℕ}
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
      sec0ErrorGame2 nx ns 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk :=
  (prEvent_breaks_le_breaksVis Guest.guest fuel budget A).trans
    (aggregate_no_forgery_vis2_at hk hs hssec fuel budget A hH hX hS hXk hSk)

/-! ### Subtree height 26 -/

section Vis2Full

attribute [local instance] Sphincs.Lifetimes.full

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 26**: a break
at V_I's trace has probability at most `sec0ErrorGame2` with leanSPHINCS's costs
`c_sk = 15166603265`, `c_ss = 23756655991`. -/
theorem aggregate_no_forgery_vis2_deployed_full {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame2 nx ns 13434881 15166603265 8630239197 23756655991 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_at sphincsKeygenBound_full sphincsSignBound_full
    Sphincs.Lifetimes.full_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 26**, at the visible bound. -/
theorem aggregate_no_forgery_vis2_deployed_full_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame2 nx ns 13434881 15166603265 8630239197 23756655991 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_game_at sphincsKeygenBound_full sphincsSignBound_full
    Sphincs.Lifetimes.full_bits fuel budget A hH hX hS hXk hSk

/-- **One slot at subtree height 26**: `2^20` keys of each scheme, `qH + budget ≤ 2^64`, `2^20`
signing requests per scheme and per key: at most `2^-42 + 2^-51`. -/
theorem aggregate_no_forgery_vis2_one_slot_full (fuel budget : ℕ)
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
  (aggregate_no_forgery_vis2_deployed_full_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame2_one_slot (by norm_num) (by norm_num) hQ hsX hsS hsXk hsSk)

/-- **A lifetime at subtree height 26**: `2^20` keys of each scheme, `qH + budget ≤ 2^64`, `2^44`
signing requests per scheme and `2^24` per key: at most `2^-41`. -/
theorem aggregate_no_forgery_vis2_lifetime_full (fuel budget : ℕ)
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
  (aggregate_no_forgery_vis2_deployed_full_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame2_lifetime_le (by norm_num) (by norm_num) hQ hsX hsS hsXk hsSk)

/-- **A lifetime with leanXMSS keys only**, `Q_v ≤ 2^64`: at most `2^-42`. -/
theorem aggregate_no_forgery_vis2_lifetime_xmss (fuel budget : ℕ) (A : GameAdversary (2 ^ 20) 0)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk)
    (hQ : qH + budget ≤ 2 ^ 64) (hsX : sX ≤ 2 ^ 44) (hsS : sS ≤ 2 ^ 44) (hsXk : sXk ≤ 2 ^ 24) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤ (2 : ℝ≥0∞)⁻¹ ^ 42 :=
  (aggregate_no_forgery_vis2_deployed_full_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame2_lifetime_xmss (by norm_num) (by norm_num) hQ hsX hsS hsXk)

/-- **A lifetime with leanXMSS keys only**, `Q_v ≤ 2^56`: at most `2^-49`. -/
theorem aggregate_no_forgery_vis2_lifetime_xmss_56 (fuel budget : ℕ) (A : GameAdversary (2 ^ 20) 0)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk)
    (hQ : qH + budget ≤ 2 ^ 56) (hsX : sX ≤ 2 ^ 44) (hsS : sS ≤ 2 ^ 44) (hsXk : sXk ≤ 2 ^ 24) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤ (2 : ℝ≥0∞)⁻¹ ^ 49 :=
  (aggregate_no_forgery_vis2_deployed_full_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame2_lifetime_xmss_56 (by norm_num) (by norm_num) hQ hsX hsS hsXk)

end Vis2Full

/-! ### Subtree height 20 -/

section Vis2Pruned20

attribute [local instance] Sphincs.Lifetimes.pruned20

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 20**: a break
at V_I's trace has probability at most `sec0ErrorGame2` with leanSPHINCS's costs
`c_sk = 236978189`, `c_ss = 8827030915`. -/
theorem aggregate_no_forgery_vis2_deployed_pruned20 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame2 nx ns 13434881 236978189 8630239197 8827030915 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_at sphincsKeygenBound_pruned20 sphincsSignBound_pruned20
    Sphincs.Lifetimes.pruned20_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 20**, at the visible bound. -/
theorem aggregate_no_forgery_vis2_deployed_pruned20_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame2 nx ns 13434881 236978189 8630239197 8827030915 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_game_at sphincsKeygenBound_pruned20 sphincsSignBound_pruned20
    Sphincs.Lifetimes.pruned20_bits fuel budget A hH hX hS hXk hSk

/-- **One slot at subtree height 20**: `2^20` keys of each scheme, `qH + budget ≤ 2^64`, `2^20`
signing requests per scheme and per key: at most `2^-42 + 2^-51`. -/
theorem aggregate_no_forgery_vis2_one_slot_pruned20 (fuel budget : ℕ)
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
  (aggregate_no_forgery_vis2_deployed_pruned20_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame2_one_slot (by norm_num) (by norm_num) hQ hsX hsS hsXk hsSk)

/-- **A lifetime at subtree height 20**: `2^20` keys of each scheme, `qH + budget ≤ 2^64`, `2^44`
signing requests per scheme and `2^24` per key: at most `2^-41`. -/
theorem aggregate_no_forgery_vis2_lifetime_pruned20 (fuel budget : ℕ)
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
  (aggregate_no_forgery_vis2_deployed_pruned20_game fuel budget A hH hX hS hXk hSk).trans
    (sec0ErrorGame2_lifetime_le (by norm_num) (by norm_num) hQ hsX hsS hsXk hsSk)

end Vis2Pruned20

/-! ### Subtree height 14 -/

section Vis2Pruned14

attribute [local instance] Sphincs.Lifetimes.pruned14

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 14**: a break
at V_I's trace has probability at most `sec0ErrorGame2` with leanSPHINCS's costs
`c_sk = 3702809`, `c_ss = 8593755535`. -/
theorem aggregate_no_forgery_vis2_deployed_pruned14 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame2 nx ns 13434881 3702809 8630239197 8593755535 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 3702556 by decide])
    Sphincs.Lifetimes.pruned14_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 14**, at the visible bound. -/
theorem aggregate_no_forgery_vis2_deployed_pruned14_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame2 nx ns 13434881 3702809 8630239197 8593755535 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_game_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 3702556 by decide])
    Sphincs.Lifetimes.pruned14_bits fuel budget A hH hX hS hXk hSk

end Vis2Pruned14

/-! ### Subtree height 13 -/

section Vis2Pruned13

attribute [local instance] Sphincs.Lifetimes.pruned13

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 13**: a break
at V_I's trace has probability at most `sec0ErrorGame2` with leanSPHINCS's costs
`c_sk = 1851419`, `c_ss = 8591904145`. -/
theorem aggregate_no_forgery_vis2_deployed_pruned13 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame2 nx ns 13434881 1851419 8630239197 8591904145 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 1851166 by decide])
    Sphincs.Lifetimes.pruned13_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 13**, at the visible bound. -/
theorem aggregate_no_forgery_vis2_deployed_pruned13_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame2 nx ns 13434881 1851419 8630239197 8591904145 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_game_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 1851166 by decide])
    Sphincs.Lifetimes.pruned13_bits fuel budget A hH hX hS hXk hSk

end Vis2Pruned13

/-! ### Subtree height 12 -/

section Vis2Pruned12

attribute [local instance] Sphincs.Lifetimes.pruned12

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 12**: a break
at V_I's trace has probability at most `sec0ErrorGame2` with leanSPHINCS's costs
`c_sk = 925725`, `c_ss = 8590978451`. -/
theorem aggregate_no_forgery_vis2_deployed_pruned12 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame2 nx ns 13434881 925725 8630239197 8590978451 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 925472 by decide])
    Sphincs.Lifetimes.pruned12_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 12**, at the visible bound. -/
theorem aggregate_no_forgery_vis2_deployed_pruned12_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame2 nx ns 13434881 925725 8630239197 8590978451 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_game_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 925472 by decide])
    Sphincs.Lifetimes.pruned12_bits fuel budget A hH hX hS hXk hSk

end Vis2Pruned12

/-! ### Subtree height 10 -/

section Vis2Pruned10

attribute [local instance] Sphincs.Lifetimes.pruned10

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 10**: a break
at V_I's trace has probability at most `sec0ErrorGame2` with leanSPHINCS's costs
`c_sk = 231457`, `c_ss = 8590284183`. -/
theorem aggregate_no_forgery_vis2_deployed_pruned10 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame2 nx ns 13434881 231457 8630239197 8590284183 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 231204 by decide])
    Sphincs.Lifetimes.pruned10_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 10**, at the visible bound. -/
theorem aggregate_no_forgery_vis2_deployed_pruned10_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame2 nx ns 13434881 231457 8630239197 8590284183 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_game_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 231204 by decide])
    Sphincs.Lifetimes.pruned10_bits fuel budget A hH hX hS hXk hSk

end Vis2Pruned10

/-! ### Subtree height 8 -/

section Vis2Pruned8

attribute [local instance] Sphincs.Lifetimes.pruned8

/-- **No forgery with the visible accounting, fully instantiated, at subtree height 8**: a break
at V_I's trace has probability at most `sec0ErrorGame2` with leanSPHINCS's costs
`c_sk = 57893`, `c_ss = 8590110619`. -/
theorem aggregate_no_forgery_vis2_deployed_pruned8 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame2 nx ns 13434881 57893 8630239197 8590110619 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 57640 by decide])
    Sphincs.Lifetimes.pruned8_bits fuel budget A hH hX hS hXk hSk

/-- **Today's event at subtree height 8**, at the visible bound. -/
theorem aggregate_no_forgery_vis2_deployed_pruned8_game {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns)
    {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      sec0ErrorGame2 nx ns 13434881 57893 8630239197 8590110619 384 686 qH budget sX sS sXk sSk :=
  aggregate_no_forgery_vis2_game_at (by decide) (by rw [sphincsSignBound_eq, show sphincsPathBound = 57640 by decide])
    Sphincs.Lifetimes.pruned8_bits fuel budget A hH hX hS hXk hSk

end Vis2Pruned8

end LeanVM.E2E
