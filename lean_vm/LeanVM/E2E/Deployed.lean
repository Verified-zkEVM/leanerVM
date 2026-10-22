import LeanVM.E2E.NoForgeryClosed
import XmssSecurity
import Sphincs.LifetimesMultiKey

/-!
# No forgery (T5), fully instantiated

**Internal** (decision E2E-12): superseded as an end theorem by `LeanVM/E2E/Main.lean`, which
states the whole result. Kept as proved; its axiom pins are in `tests/LeanVMTests/E2E/Pins.lean`.

`aggregate_no_forgery` at leanXMSS's proved multi-user security
(`XmssSecurity.leanXmss_has_multi_user_security`), leanSPHINCS's proved multi-user bound
(`Sphincs.Lifetimes.requestedMultiUserKey`, at each proved parameter set) and the proved costs of
the honest signers and the final verifications (`aggregate_no_forgery_closed`). The game is
generic in the leanSPHINCS parameter set (`[Sphincs.Params]`: key generation and signing depend
on the subtree height `b`, verification does not, and the deployed guest only verifies), so there
is one theorem per proved set, `aggregate_no_forgery_deployed_full` (`b = 26`),
`…_pruned20`, `…_pruned14`, `…_pruned13`, `…_pruned12`, `…_pruned10` and `…_pruned8`. Their only
hypotheses are the adversary's query bounds (`qH` hash queries, `sX` leanXMSS and `sS`
leanSPHINCS signing requests) and `Q + 384 < 2^126`, `Q` the game's hash queries

  `Q = 13,434,881 n_x + csk_b n_s + qH + 8,630,239,197 sX + css_b sS + budget`

(`csk_b`, `css_b` leanSPHINCS's key generation and signature costs at `b`); the bound is
`closedError Q n_x n_s`:

  `Q (2^-128 + 5Q/2^256) + Q (2/2^192 + 4(Q+1)/2^256) + Q (14/2^192 + 4Q/2^256) + Q(Q+1)/2^193`
  `+ (Q+384)/2^127 + n_x²/2^127 + (Q+384)²/2^252 + n_s (Q+686)/2^127`.

`aggregate_no_forgery_deployed_full_sharp` and `…_pruned20_sharp` keep leanSPHINCS's per-key
bound `Multi.multiBound` itself (about `q (1.75 + 0.002 n_s) / 2^128` at `b = 26`, lean_sphincs's
`PROOF.md`, against `2 n_s q / 2^128`). `aggregate_no_forgery_one_slot_full` and `…_pruned20`
evaluate the bound at `n_x = n_s = 2^20` keys, `qH + budget ≤ 2^64` and `2^20` signing requests
per scheme: at most `2^-42`.

The lean_xmss and lean_sphincs endpoints live in non-module files, so this file is not a module.
The costs agree with the schemes' own counts: `xmssKeygenBound` is lean_xmss's
`XmssSecurity.Bridge.keygenQueries` and `sphincsKeygenBound` lean_sphincs's `keygenCost + 1`
(`xmssKeygenBound_eq_keygenQueries`, `sphincsKeygenBound_eq_keygenCost`).
-/

namespace LeanVM.E2E

open OracleSpec OracleComp
open scoped ENNReal

/-! ### The costs against the schemes' own counts -/

/-- leanXMSS's key-generation bound is lean_xmss's exact count. -/
theorem xmssKeygenBound_eq_keygenQueries : xmssKeygenBound = XmssSecurity.Bridge.keygenQueries := by
  rw [xmssKeygenBound_eq, XmssSecurity.Bridge.keygenQueries_eq]

/-- leanSPHINCS's key-generation bound is lean_sphincs's credited cost and the seed hash. -/
theorem sphincsKeygenBound_eq_keygenCost [Sphincs.Params] :
    sphincsKeygenBound = Sphincs.Security.ForsPotential.keygenCost + 1 := by
  unfold sphincsKeygenBound Sphincs.Security.ForsPotential.keygenCost
  omega

/-! ### The instantiation, generic in the parameter set -/

/-- Every proved leanSPHINCS bound is at most `n · q / 2^127`. -/
theorem multiBound_le [Sphincs.Params] (n qh : ℕ) (ρ : ℝ) (B c : ℚ) (q : ℕ) :
    Sphincs.Security.Multi.multiBound n qh ρ B c q ≤
      n * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞)) := by
  unfold Sphincs.Security.Multi.multiBound
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

/-- The game's hash queries at a parameter set with leanSPHINCS costs `csk`, `css`. -/
theorem gameQueries_eq [Sphincs.Params] {csk css : ℕ} (hk : sphincsKeygenBound = csk)
    (hs : sphincsSignBound = css) (nx ns qH sX sS budget : ℕ) :
    gameQueries nx ns qH sX sS budget =
      nx * 13434881 + ns * csk + (qH + sX * 8630239197 + sS * css) + budget := by
  have hx : xmssSignBound = 8630239197 := by rw [xmssSignBound_eq]; norm_num
  rw [gameQueries, xmssKeygenBound_eq, hx, hk, hs]

/-- **No forgery at a parameter set**, from its multi-user bound and its costs. -/
theorem aggregate_no_forgery_at [Sphincs.Params] {nx ns csk css : ℕ}
    (hk : sphincsKeygenBound = csk) (hs : sphincsSignBound = css) {εs : ℕ → ℝ≥0∞}
    (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs)
    (hε : ∀ q, εs q ≤ ns * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞)))
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * 13434881 + ns * csk + (qH + sX * 8630239197 + sS * css) + budget + 384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      closedError (nx * 13434881 + ns * csk + (qH + sX * 8630239197 + sS * css) + budget) nx ns := by
  have e := gameQueries_eq hk hs nx ns qH sX sS budget
  have h := aggregate_no_forgery_closed XmssSecurity.leanXmss_has_multi_user_security hsph hε fuel
    budget A hH hX hS (by rw [e]; exact hq)
  rwa [e] at h

/-- The error at `n_x = n_s = 2^20`, `qH + budget ≤ 2^64` and `2^20` signing requests per scheme,
with leanSPHINCS's costs `csk ≤ 2^34` and `css ≤ 2^35`: at most `2^-42`. -/
theorem closedError_one_slot {csk css qH sX sS budget : ℕ} (hk : csk ≤ 2 ^ 34) (hs : css ≤ 2 ^ 35)
    (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 20) (hS : sS ≤ 2 ^ 20) :
    2 ^ 20 * 13434881 + 2 ^ 20 * csk + (qH + sX * 8630239197 + sS * css) + budget + 384 < 2 ^ 126 ∧
      closedError (2 ^ 20 * 13434881 + 2 ^ 20 * csk + (qH + sX * 8630239197 + sS * css) + budget)
        (2 ^ 20) (2 ^ 20) ≤ (2 : ℝ≥0∞)⁻¹ ^ 42 := by
  have h1 : sX * 8630239197 ≤ 2 ^ 20 * 8630239197 := Nat.mul_le_mul_right _ hX
  have h2 : sS * css ≤ 2 ^ 20 * 2 ^ 35 := Nat.mul_le_mul hS hs
  have h3 : 2 ^ 20 * csk ≤ 2 ^ 20 * 2 ^ 34 := Nat.mul_le_mul_left _ hk
  have hle : 2 ^ 20 * 13434881 + 2 ^ 20 * csk + (qH + sX * 8630239197 + sS * css) + budget ≤
      2 ^ 20 * 13434881 + 2 ^ 20 * 2 ^ 34 + (2 ^ 64 + 2 ^ 20 * 8630239197 + 2 ^ 20 * 2 ^ 35) := by
    linarith
  refine ⟨lt_of_le_of_lt (Nat.add_le_add_right hle 384) (by norm_num),
    closedError_le_of_num (by norm_num) ((closedNum_mono hle le_rfl le_rfl).trans ?_)⟩
  unfold closedNum
  norm_num

/-! ### Subtree height 26 -/

section Full

attribute [local instance] Sphincs.Lifetimes.full

theorem sphincsKeygenBound_full : sphincsKeygenBound = 15166603265 := by decide

theorem sphincsSignBound_full : sphincsSignBound = 23756655991 := by
  rw [sphincsSignBound_eq, show sphincsPathBound = 15166603012 by decide]

/-- leanSPHINCS's proved multi-user bound at subtree height 26 (`full_multiUserKey`). -/
noncomputable abbrev fullMultiBound (n : ℕ) : ℕ → ℝ≥0∞ :=
  Sphincs.Security.Multi.multiBound n 250752950924986904089568310569467904
    (Sphincs.Security.H0.rho_b26 : ℝ) Sphincs.Security.H0.small_b26.B
    ((2 - Sphincs.Security.H0.rho_b26 +
      ((250752950924986904089568310569467904 : ℕ) : ℚ) / 2 ^ 128 +
      ((1383000000 : ℕ) : ℚ) * 123 / (2 ^ 26 * 2 ^ 15)) *
      ((2 ^ 26 * Sphincs.Security.H0.near_b26.En : ℚ) / 2))

/-- **No forgery, fully instantiated, at subtree height 26.** For the game of the deployed guest
with `n_x` leanXMSS and `n_s` leanSPHINCS keys (subtree height 26) and an adversary making at
most `qH` hash queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests, with
`Q = 13,434,881 n_x + 15,166,603,265 n_s + qH + 8,630,239,197 sX + 23,756,655,991 sS + budget`
and `Q + 384 < 2^126`: V_I accepts a root statement with a forged claim of an honest key or an
unbacked DA claim with probability at most `closedError Q n_x n_s`. -/
theorem aggregate_no_forgery_deployed_full {nx ns : ℕ} (fuel budget : ℕ) (A : GameAdversary nx ns)
    {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * 13434881 + ns * 15166603265 + (qH + sX * 8630239197 + sS * 23756655991) + budget +
      384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      closedError (nx * 13434881 + ns * 15166603265 + (qH + sX * 8630239197 + sS * 23756655991) +
        budget) nx ns :=
  aggregate_no_forgery_at sphincsKeygenBound_full sphincsSignBound_full
    (Sphincs.Lifetimes.full_multiUserKey ns) (multiBound_le ns _ _ _ _) fuel budget A hH hX hS hq

/-- **No forgery at subtree height 26, with leanSPHINCS's per-key bound** `fullMultiBound` (the
leanXMSS and chain terms of `closedError`, the leanSPHINCS term `fullMultiBound n_s (Q + 686)`). -/
theorem aggregate_no_forgery_deployed_full_sharp {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * 13434881 + ns * 15166603265 + (qH + sX * 8630239197 + sS * 23756655991) + budget +
      384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      noForgeryError (nx * 13434881 + ns * 15166603265 + (qH + sX * 8630239197 + sS * 23756655991) +
        budget) nx 384 686 (fullMultiBound ns) := by
  have e := gameQueries_eq sphincsKeygenBound_full sphincsSignBound_full nx ns qH sX sS budget
  have h := aggregate_no_forgery XmssSecurity.leanXmss_has_multi_user_security
    (Sphincs.Lifetimes.full_multiUserKey ns) keygenFromSeed_isTotalQueryBound
    sphincsKeygenFromSeed_isTotalQueryBound sign_isTotalQueryBound sphincsSign_isTotalQueryBound
    verify_isTotalQueryBound sphincsVerify_isTotalQueryBound fuel budget A hH hX hS
    (by rw [← gameQueries, e]; exact hq)
  rwa [← gameQueries, e] at h

/-- **One slot at subtree height 26**: `2^20` keys of each scheme, `qH + budget ≤ 2^64` and `2^20`
signing requests per scheme give an error of at most `2^-42`. -/
theorem aggregate_no_forgery_one_slot_full (fuel budget : ℕ) (A : GameAdversary (2 ^ 20) (2 ^ 20))
    {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hQ : qH + budget ≤ 2 ^ 64) (hsX : sX ≤ 2 ^ 20) (hsS : sS ≤ 2 ^ 20) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤ (2 : ℝ≥0∞)⁻¹ ^ 42 :=
  have h := closedError_one_slot (csk := 15166603265) (css := 23756655991) (by norm_num)
    (by norm_num) hQ hsX hsS
  (aggregate_no_forgery_deployed_full fuel budget A hH hX hS h.1).trans h.2

end Full

/-! ### Subtree height 20 -/

section Pruned20

attribute [local instance] Sphincs.Lifetimes.pruned20

theorem sphincsKeygenBound_pruned20 : sphincsKeygenBound = 236978189 := by decide

theorem sphincsSignBound_pruned20 : sphincsSignBound = 8827030915 := by
  rw [sphincsSignBound_eq, show sphincsPathBound = 236977936 by decide]

/-- leanSPHINCS's proved multi-user bound at subtree height 20 (`pruned20_multiUserKey`). -/
noncomputable abbrev pruned20MultiBound (n : ℕ) : ℕ → ℝ≥0∞ :=
  Sphincs.Security.Multi.multiBound n 558871528355207643822193711415033856
    (Sphincs.Security.H0.rho_b20 : ℝ) Sphincs.Security.H0.small_b20.B
    ((2 - Sphincs.Security.H0.rho_b20 +
      ((558871528355207643822193711415033856 : ℕ) : ℚ) / 2 ^ 128 +
      ((26030000 : ℕ) : ℚ) * 123 / (2 ^ 20 * 2 ^ 15)) *
      ((2 ^ 20 * Sphincs.Security.H0.near_b20.En : ℚ) / 2))

/-- **No forgery, fully instantiated, at subtree height 20**, with
`Q = 13,434,881 n_x + 236,978,189 n_s + qH + 8,630,239,197 sX + 8,827,030,915 sS + budget`. -/
theorem aggregate_no_forgery_deployed_pruned20 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * 13434881 + ns * 236978189 + (qH + sX * 8630239197 + sS * 8827030915) + budget +
      384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      closedError (nx * 13434881 + ns * 236978189 + (qH + sX * 8630239197 + sS * 8827030915) +
        budget) nx ns :=
  aggregate_no_forgery_at sphincsKeygenBound_pruned20 sphincsSignBound_pruned20
    (Sphincs.Lifetimes.pruned20_multiUserKey ns) (multiBound_le ns _ _ _ _) fuel budget A hH hX hS hq

/-- **No forgery at subtree height 20, with leanSPHINCS's per-key bound** `pruned20MultiBound`. -/
theorem aggregate_no_forgery_deployed_pruned20_sharp {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * 13434881 + ns * 236978189 + (qH + sX * 8630239197 + sS * 8827030915) + budget +
      384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      noForgeryError (nx * 13434881 + ns * 236978189 + (qH + sX * 8630239197 + sS * 8827030915) +
        budget) nx 384 686 (pruned20MultiBound ns) := by
  have e := gameQueries_eq sphincsKeygenBound_pruned20 sphincsSignBound_pruned20 nx ns qH sX sS budget
  have h := aggregate_no_forgery XmssSecurity.leanXmss_has_multi_user_security
    (Sphincs.Lifetimes.pruned20_multiUserKey ns) keygenFromSeed_isTotalQueryBound
    sphincsKeygenFromSeed_isTotalQueryBound sign_isTotalQueryBound sphincsSign_isTotalQueryBound
    verify_isTotalQueryBound sphincsVerify_isTotalQueryBound fuel budget A hH hX hS
    (by rw [← gameQueries, e]; exact hq)
  rwa [← gameQueries, e] at h

/-- **One slot at subtree height 20**: at most `2^-42`. -/
theorem aggregate_no_forgery_one_slot_pruned20 (fuel budget : ℕ)
    (A : GameAdversary (2 ^ 20) (2 ^ 20)) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hQ : qH + budget ≤ 2 ^ 64) (hsX : sX ≤ 2 ^ 20) (hsS : sS ≤ 2 ^ 20) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤ (2 : ℝ≥0∞)⁻¹ ^ 42 :=
  have h := closedError_one_slot (csk := 236978189) (css := 8827030915) (by norm_num)
    (by norm_num) hQ hsX hsS
  (aggregate_no_forgery_deployed_pruned20 fuel budget A hH hX hS h.1).trans h.2

end Pruned20

/-! ### Subtree heights 14, 13, 12, 10 and 8 -/

section Pruned14

attribute [local instance] Sphincs.Lifetimes.pruned14

/-- **No forgery, fully instantiated, at subtree height 14.** -/
theorem aggregate_no_forgery_deployed_pruned14 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * 13434881 + ns * 3702809 + (qH + sX * 8630239197 + sS * 8593755535) + budget +
      384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      closedError (nx * 13434881 + ns * 3702809 + (qH + sX * 8630239197 + sS * 8593755535) +
        budget) nx ns :=
  aggregate_no_forgery_at (by decide)
    (by rw [sphincsSignBound_eq, show sphincsPathBound = 3702556 by decide])
    (Sphincs.Lifetimes.pruned14_multiUserKey ns) (multiBound_le ns _ _ _ _) fuel budget A hH hX hS hq

end Pruned14

section Pruned13

attribute [local instance] Sphincs.Lifetimes.pruned13

/-- **No forgery, fully instantiated, at subtree height 13.** -/
theorem aggregate_no_forgery_deployed_pruned13 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * 13434881 + ns * 1851419 + (qH + sX * 8630239197 + sS * 8591904145) + budget +
      384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      closedError (nx * 13434881 + ns * 1851419 + (qH + sX * 8630239197 + sS * 8591904145) +
        budget) nx ns :=
  aggregate_no_forgery_at (by decide)
    (by rw [sphincsSignBound_eq, show sphincsPathBound = 1851166 by decide])
    (Sphincs.Lifetimes.pruned13_multiUserKey ns) (multiBound_le ns _ _ _ _) fuel budget A hH hX hS hq

end Pruned13

section Pruned12

attribute [local instance] Sphincs.Lifetimes.pruned12

/-- **No forgery, fully instantiated, at subtree height 12** (the kept height of the Rust test
signers, `LEAN_LEAN_SPHINCS_KEPT_HEIGHT`). -/
theorem aggregate_no_forgery_deployed_pruned12 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * 13434881 + ns * 925725 + (qH + sX * 8630239197 + sS * 8590978451) + budget +
      384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      closedError (nx * 13434881 + ns * 925725 + (qH + sX * 8630239197 + sS * 8590978451) +
        budget) nx ns :=
  aggregate_no_forgery_at (by decide)
    (by rw [sphincsSignBound_eq, show sphincsPathBound = 925472 by decide])
    (Sphincs.Lifetimes.pruned12_multiUserKey ns) (multiBound_le ns _ _ _ _) fuel budget A hH hX hS hq

end Pruned12

section Pruned10

attribute [local instance] Sphincs.Lifetimes.pruned10

/-- **No forgery, fully instantiated, at subtree height 10.** -/
theorem aggregate_no_forgery_deployed_pruned10 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * 13434881 + ns * 231457 + (qH + sX * 8630239197 + sS * 8590284183) + budget +
      384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      closedError (nx * 13434881 + ns * 231457 + (qH + sX * 8630239197 + sS * 8590284183) +
        budget) nx ns :=
  aggregate_no_forgery_at (by decide)
    (by rw [sphincsSignBound_eq, show sphincsPathBound = 231204 by decide])
    (Sphincs.Lifetimes.pruned10_multiUserKey ns) (multiBound_le ns _ _ _ _) fuel budget A hH hX hS hq

end Pruned10

section Pruned8

attribute [local instance] Sphincs.Lifetimes.pruned8

/-- **No forgery, fully instantiated, at subtree height 8.** -/
theorem aggregate_no_forgery_deployed_pruned8 {nx ns : ℕ} (fuel budget : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * 13434881 + ns * 57893 + (qH + sX * 8630239197 + sS * 8590110619) + budget +
      384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      closedError (nx * 13434881 + ns * 57893 + (qH + sX * 8630239197 + sS * 8590110619) +
        budget) nx ns :=
  aggregate_no_forgery_at (by decide)
    (by rw [sphincsSignBound_eq, show sphincsPathBound = 57640 by decide])
    (Sphincs.Lifetimes.pruned8_multiUserKey ns) (multiBound_le ns _ _ _ _) fuel budget A hH hX hS hq

end Pruned8

end LeanVM.E2E
