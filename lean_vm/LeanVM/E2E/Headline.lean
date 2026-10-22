import LeanVM.E2E.NoForgery2
import LeanVM.E2E.Guest
import XmssSecurity
import Sphincs.LifetimesMulti

/-!
# The headline: no forgery, `Pr[break] ≤ q · 2^-λ₁ + 30 q² / 2^256`

`aggregate_no_forgery_final`: for every leanSPHINCS parameter set (`SphincsSet`), every numbers
`n_x`, `n_s` of honest keys, every tree size `N` and every adversary (`AdvBounds`), V_I, run on at
most `N` nodes with the budget `viCost N`, accepts a root statement with a forged claim of an honest
key, or a DA claim the oracle's log does not back (`Breaks`), with probability at most

    q · noForgeryRate n_x n_s + 30 q² / 2^256,

`q = totalQueries n_x n_s qH sX sS N` every hash evaluation of the game: the honest key
generations, the adversary's `qH` queries, the `sX` leanXMSS and `sS` leanSPHINCS signatures it
requests at their proved worst-case costs, and V_I's budget `viCost N` (`totalQueries_eq`).

* **The linear rate** `noForgeryRate n_x n_s = (2^128 (3 + 2 n_s) + 2^124 + 2^106 n_x) / 2^256`,
  `2^-λ₁` with `λ₁ = 128 − log₂(3.0625 + 2 n_s + n_x/2^22) ≈ 127 − log₂(n_s + 1.53)`: V°'s `2^-128`
  (T1), leanXMSS's multi-user `2^-127` (free of `n_x`), leanSPHINCS's `n_s/2^127`; the constants
  (`384/2^127`, `n_x²/2^127`, `686 n_s/2^127`) are paid by the key generations `q` counts
  (`keygens_le_gameQueries`). `λ₁ = 106` at `2^20 + 2^20` keys (`noForgeryRate_deployed`, the
  exact value `106.999998`), `126` with leanXMSS keys only (`noForgeryRate_xmss_only`), `127 − k`
  whenever `n_s + 2 ≤ 2^k` (`noForgeryRate_le`).
* **The quadratic term** `30 q²/2^256`: the failures' `13` (T1, W6, E5), leanXMSS's `q²/2^252`
  (`16`), and T3's `q³/(6 · 2^384) ≤ q²/2^256` (`1`, `predError2_le_sq`).
* **No side condition.** leanXMSS's multi-user theorem asks `q + 384 < 2^126`; past it,
  `30 q²/2^256 ≥ 1` (`one_le_quad_of_large`) and the bound is trivial.

The proof is T5 with the cubic T3 (`NoForgery2.lean`: `prEvent_game_aggBad2_le`,
`forged_of_breaks2`, `prEvent_forgedX_le_bound2`, `prEvent_forgedS_le_bound2`) at leanXMSS's proved
multi-user security and leanSPHINCS's proved multi-user bound, and arithmetic. The design and the
alternatives: `docs/roadmap/headline.md`.

`SphincsSet` holds a parameter set's costs and its closed multi-user bound `n q/2^127`. A sharper
leanSPHINCS rate is a later, additive extension (a class extending `SphincsSet` with the sharp bound
and its own rate), with no change to this file.

The lean_xmss and lean_sphincs endpoints live in non-module files, so this file is not a module.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open LeanVM.Protocol.EndToEnd.Sound OracleSpec OracleComp
open scoped ENNReal

/-! ## The parameter sets, the adversary, V_I's budget -/

/-- **A leanSPHINCS parameter set with its proved costs and multi-user bound.** One instance per
proved set: `full` (`b = 26`), `pruned20`, `pruned14`, `pruned13`, `pruned12`, `pruned10`,
`pruned8`. -/
class SphincsSet (P : Sphincs.Params) where
  /-- Key generation's hash calls (`sphincsKeygenBound`). -/
  keygenCost : ℕ
  /-- A signature's hash calls (`sphincsSignBound`). -/
  signCost : ℕ
  keygen_eq : @sphincsKeygenBound P = keygenCost
  sign_eq : @sphincsSignBound P = signCost
  /-- Every proved set's key generation makes at least `2^15` calls (`b = 8`: `57,893`). -/
  keygen_ge : 2 ^ 15 ≤ keygenCost
  /-- The multi-user bound at `n` keys: `n q / 2^127` (`Sphincs.Lifetimes.requestedMultiUser`). -/
  multi : ∀ n, @Sphincs.Security.Multi.HasMultiUserBound P n
    (fun q => n * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞)))

/-- Subtree height 26. -/
instance sphincsSetFull : SphincsSet Sphincs.Lifetimes.full where
  keygenCost := 15166603265
  signCost := 23756655991
  keygen_eq := by decide
  sign_eq := by
    rw [@sphincsSignBound_eq Sphincs.Lifetimes.full,
      show @sphincsPathBound Sphincs.Lifetimes.full = 15166603012 by decide]
  keygen_ge := by norm_num
  multi n := (Sphincs.Lifetimes.requestedMultiUser n).1

/-- Subtree height 20. -/
instance sphincsSetPruned20 : SphincsSet Sphincs.Lifetimes.pruned20 where
  keygenCost := 236978189
  signCost := 8827030915
  keygen_eq := by decide
  sign_eq := by
    rw [@sphincsSignBound_eq Sphincs.Lifetimes.pruned20,
      show @sphincsPathBound Sphincs.Lifetimes.pruned20 = 236977936 by decide]
  keygen_ge := by norm_num
  multi n := (Sphincs.Lifetimes.requestedMultiUser n).2.1

/-- Subtree height 14. -/
instance sphincsSetPruned14 : SphincsSet Sphincs.Lifetimes.pruned14 where
  keygenCost := 3702809
  signCost := 8593755535
  keygen_eq := by decide
  sign_eq := by
    rw [@sphincsSignBound_eq Sphincs.Lifetimes.pruned14,
      show @sphincsPathBound Sphincs.Lifetimes.pruned14 = 3702556 by decide]
  keygen_ge := by norm_num
  multi n := (Sphincs.Lifetimes.requestedMultiUser n).2.2.1

/-- Subtree height 13. -/
instance sphincsSetPruned13 : SphincsSet Sphincs.Lifetimes.pruned13 where
  keygenCost := 1851419
  signCost := 8591904145
  keygen_eq := by decide
  sign_eq := by
    rw [@sphincsSignBound_eq Sphincs.Lifetimes.pruned13,
      show @sphincsPathBound Sphincs.Lifetimes.pruned13 = 1851166 by decide]
  keygen_ge := by norm_num
  multi n := (Sphincs.Lifetimes.requestedMultiUser n).2.2.2.1

/-- Subtree height 12 (the Rust test signers' kept height). -/
instance sphincsSetPruned12 : SphincsSet Sphincs.Lifetimes.pruned12 where
  keygenCost := 925725
  signCost := 8590978451
  keygen_eq := by decide
  sign_eq := by
    rw [@sphincsSignBound_eq Sphincs.Lifetimes.pruned12,
      show @sphincsPathBound Sphincs.Lifetimes.pruned12 = 925472 by decide]
  keygen_ge := by norm_num
  multi n := (Sphincs.Lifetimes.requestedMultiUser n).2.2.2.2.1

/-- Subtree height 10. -/
instance sphincsSetPruned10 : SphincsSet Sphincs.Lifetimes.pruned10 where
  keygenCost := 231457
  signCost := 8590284183
  keygen_eq := by decide
  sign_eq := by
    rw [@sphincsSignBound_eq Sphincs.Lifetimes.pruned10,
      show @sphincsPathBound Sphincs.Lifetimes.pruned10 = 231204 by decide]
  keygen_ge := by norm_num
  multi n := (Sphincs.Lifetimes.requestedMultiUser n).2.2.2.2.2.1

/-- Subtree height 8. -/
instance sphincsSetPruned8 : SphincsSet Sphincs.Lifetimes.pruned8 where
  keygenCost := 57893
  signCost := 8590110619
  keygen_eq := by decide
  sign_eq := by
    rw [@sphincsSignBound_eq Sphincs.Lifetimes.pruned8,
      show @sphincsPathBound Sphincs.Lifetimes.pruned8 = 57640 by decide]
  keygen_ge := by norm_num
  multi n := (Sphincs.Lifetimes.requestedMultiUser n).2.2.2.2.2.2

/-- **What the adversary may do**: at most `qH` hash queries, `sX` leanXMSS and `sS` leanSPHINCS
signing requests, whatever the honest public keys. -/
structure AdvBounds {nx ns : ℕ} (A : GameAdversary nx ns) (qH sX sS : ℕ) : Prop where
  hash : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH
  xmss : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX
  sphincs : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS

/-- **V_I's per-node budget.** A definition: no-forgery holds for every budget, so this value only
enters `q`. That the honest V_I stays within it on every node is a completeness obligation, not
proved here. -/
def viNodeCost : ℕ := 2 ^ 40

/-- **V_I's budget on trees of at most `N` nodes.** -/
def viCost (N : ℕ) : ℕ := N * viNodeCost

/-- **`q`: every hash evaluation of the game** on trees of at most `N` nodes: the honest key
generations, the adversary's queries, the signatures it requests, and V_I's budget. -/
def totalQueries [Sphincs.Params] (nx ns qH sX sS N : ℕ) : ℕ :=
  gameQueries nx ns qH sX sS (viCost N)

/-- `q` at the proved costs. -/
theorem totalQueries_eq [P : Sphincs.Params] [S : SphincsSet P] (nx ns qH sX sS N : ℕ) :
    totalQueries nx ns qH sX sS N =
      nx * 13434881 + ns * S.keygenCost + qH + sX * 8630239197 + sS * S.signCost + viCost N := by
  have hx : xmssSignBound = 8630239197 := by rw [xmssSignBound_eq]; norm_num
  rw [totalQueries, gameQueries, xmssKeygenBound_eq, hx, S.keygen_eq, S.sign_eq]
  ring

/-- The game's hash evaluations pay for the key generations. -/
theorem keygens_le_gameQueries [P : Sphincs.Params] [S : SphincsSet P]
    (nx ns qH sX sS budget : ℕ) :
    nx * 2 ^ 23 + ns * 2 ^ 15 ≤ gameQueries nx ns qH sX sS budget := by
  have hx : 2 ^ 23 ≤ xmssKeygenBound := by rw [xmssKeygenBound_eq]; norm_num
  have hs : 2 ^ 15 ≤ sphincsKeygenBound := S.keygen_eq ▸ S.keygen_ge
  have h1 : nx * 2 ^ 23 ≤ nx * xmssKeygenBound := Nat.mul_le_mul_left _ hx
  have h2 : ns * 2 ^ 15 ≤ ns * sphincsKeygenBound := Nat.mul_le_mul_left _ hs
  unfold gameQueries
  exact le_trans (Nat.add_le_add h1 h2) (Nat.le_add_right_of_le (Nat.le_add_right _ _))

/-! ## The rates -/

/-- The linear rate times `2^256`. -/
def noForgeryRateNum (nx ns : ℕ) : ℕ := 2 ^ 128 * (3 + 2 * ns) + 2 ^ 124 + 2 ^ 106 * nx

/-- **The linear rate `2^-λ₁`**: `(3 + 2 n_s + 1/16 + n_x/2^22)/2^128`. -/
noncomputable def noForgeryRate (nx ns : ℕ) : ℝ≥0∞ := (noForgeryRateNum nx ns : ℝ≥0∞) / 2 ^ 256

/-- **`λ₁ = 127 − k`** once `n_s + 2 ≤ 2^k` (and `n_x ≤ 2^21`). -/
theorem noForgeryRate_le {nx ns k : ℕ} (hk : k ≤ 127) (hx : nx ≤ 2 ^ 21) (hs : ns + 2 ≤ 2 ^ k) :
    noForgeryRate nx ns ≤ (2 : ℝ≥0∞)⁻¹ ^ (127 - k) := by
  have e : 2 ^ (256 - (127 - k)) = 2 ^ 129 * 2 ^ k := by
    rw [← pow_add]; congr 1; omega
  have hn : noForgeryRateNum nx ns ≤ 2 ^ (256 - (127 - k)) := by
    rw [e]
    unfold noForgeryRateNum
    have : 2 ^ 106 * nx ≤ 2 ^ 127 := by
      calc 2 ^ 106 * nx ≤ 2 ^ 106 * 2 ^ 21 := Nat.mul_le_mul_left _ hx
        _ = 2 ^ 127 := by norm_num
    nlinarith [Nat.mul_le_mul_left (2 ^ 129) hs]
  rw [noForgeryRate, ← ENNReal.inv_pow, inv_two_pow_eq (127 - k) (by omega), div_eq_mul_inv]
  gcongr
  exact_mod_cast hn

/-- **`2^20 + 2^20` keys: `λ₁ = 106`** (the rate is `(2^21 + 3.3125)/2^128`, `λ₁ ≈ 106.999998`). -/
theorem noForgeryRate_deployed : noForgeryRate (2 ^ 20) (2 ^ 20) ≤ (2 : ℝ≥0∞)⁻¹ ^ 106 :=
  noForgeryRate_le (k := 21) (by norm_num) (by norm_num) (by norm_num)

/-- **leanXMSS keys only (`n_x ≤ 2^21`): `λ₁ = 126`.** -/
theorem noForgeryRate_xmss_only {nx : ℕ} (hx : nx ≤ 2 ^ 21) :
    noForgeryRate nx 0 ≤ (2 : ℝ≥0∞)⁻¹ ^ 126 :=
  noForgeryRate_le (k := 1) (by norm_num) hx (by norm_num)

/-! ## The error as fractions over `2^256` -/

/-- The chain's bad events without T3 (T1, W6, E5), times `2^256`. -/
def chainCoreNum (Q : ℕ) : ℕ :=
  2 ^ 128 * Q + 5 * Q * Q + 2 ^ 65 * Q + 4 * Q * (Q + 1) + 14 * 2 ^ 64 * Q + 4 * Q * Q

/-- leanXMSS's multi-user bound (`xmssMultiError`) times `2^256`. -/
def xmssMultiNum (nx q : ℕ) : ℕ := 2 ^ 129 * q + 2 ^ 129 * nx ^ 2 + 16 * q ^ 2

/-- The chain's bad events: T1, W6, E5 as one fraction, and T3's cube. -/
theorem aggBadError2_eq_core (Q : ℕ) :
    aggBadError2 Q = (chainCoreNum Q : ℝ≥0∞) / 2 ^ 256 + predError2 Q := by
  set I := ((2 : ℝ≥0∞) ^ 256)⁻¹
  have h128 : ((2 : ℝ≥0∞) ^ 128)⁻¹ = 2 ^ 128 * I := inv_two_pow_eq 128 (by norm_num)
  have h192 : ((2 : ℝ≥0∞) ^ 192)⁻¹ = 2 ^ 64 * I := inv_two_pow_eq 192 (by norm_num)
  have hs : (4 + leanVmSeeds.steps.length) * Q = 5 * Q := rfl
  simp only [aggBadError2, εLean, failBound, hs, chainCoreNum, div_eq_mul_inv, ← ENNReal.inv_pow,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_one, h128, h192]
  ring

theorem xmssMultiError_eq_num (nx q : ℕ) :
    xmssMultiError nx q = (xmssMultiNum nx q : ℝ≥0∞) / 2 ^ 256 := by
  set I := ((2 : ℝ≥0∞) ^ 256)⁻¹
  have h127 : ((2 : ℝ≥0∞) ^ 127)⁻¹ = 2 ^ 129 * I := inv_two_pow_eq 127 (by norm_num)
  have h252 : ((2 : ℝ≥0∞) ^ 252)⁻¹ = 2 ^ 4 * I := inv_two_pow_eq 252 (by norm_num)
  simp only [xmssMultiError, xmssMultiNum, div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_mul, Nat.cast_add, h127, h252]
  ring

theorem sphincsMultiClosed_eq_num (ns q : ℕ) :
    (ns : ℝ≥0∞) * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞)) =
      ((2 ^ 129 * (ns * q) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  set I := ((2 : ℝ≥0∞) ^ 256)⁻¹
  have h127 : ((2 : ℝ≥0∞) ^ 127)⁻¹ = 2 ^ 129 * I := inv_two_pow_eq 127 (by norm_num)
  simp only [div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, h127]
  ring

/-! ## Linear plus quadratic -/

/-- **Every term but T3's is linear plus `29 q²`** (over `2^256`): the failures' `13 q²` and
leanXMSS's `16 q²`. The key generations (`n_x 2^23 + n_s 2^15 ≤ Q`) pay the constants. -/
theorem chainCoreNum_le {nx ns Q : ℕ} (hQ : nx * 2 ^ 23 + ns * 2 ^ 15 ≤ Q) :
    chainCoreNum Q + (if nx = 0 then 0 else xmssMultiNum nx (Q + 384)) +
        2 ^ 129 * (ns * (Q + 686)) ≤
      Q * noForgeryRateNum nx ns + 29 * Q ^ 2 := by
  have h3 : 2 ^ 129 * (ns * 686) ≤ 2 ^ 114 * 686 * Q := by
    have : ns * 2 ^ 15 ≤ Q := le_trans (Nat.le_add_left _ _) hQ
    calc 2 ^ 129 * (ns * 686) = 2 ^ 114 * 686 * (ns * 2 ^ 15) := by ring
      _ ≤ 2 ^ 114 * 686 * Q := Nat.mul_le_mul_left _ this
  split_ifs with hnx
  · subst hnx
    unfold chainCoreNum noForgeryRateNum
    nlinarith [h3]
  · have hx1 : 1 ≤ nx := Nat.one_le_iff_ne_zero.mpr hnx
    have hxQ : nx * 2 ^ 23 ≤ Q := le_trans (Nat.le_add_right _ _) hQ
    have hQ23 : 2 ^ 23 ≤ Q := le_trans (by nlinarith) hxQ
    have h1 : 2 ^ 129 * nx ^ 2 ≤ 2 ^ 106 * nx * Q := by
      calc 2 ^ 129 * nx ^ 2 = 2 ^ 106 * nx * (nx * 2 ^ 23) := by ring
        _ ≤ 2 ^ 106 * nx * Q := Nat.mul_le_mul_left _ hxQ
    have h2 : 2 ^ 129 * 384 ≤ 2 ^ 106 * 384 * Q := by
      calc 2 ^ 129 * 384 = 2 ^ 106 * 384 * 2 ^ 23 := by ring
        _ ≤ 2 ^ 106 * 384 * Q := Nat.mul_le_mul_left _ hQ23
    unfold chainCoreNum xmssMultiNum noForgeryRateNum
    nlinarith [h1, h2, h3, hQ23]

/-- `chainCoreNum_le` in `ℝ≥0∞`. -/
theorem noForgery_core_le {nx ns Q : ℕ} (hQ : nx * 2 ^ 23 + ns * 2 ^ 15 ≤ Q) :
    (chainCoreNum Q : ℝ≥0∞) / 2 ^ 256 + (if nx = 0 then 0 else xmssMultiError nx (Q + 384)) +
        (ns : ℝ≥0∞) * (((Q + 686 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞)) ≤
      Q * noForgeryRate nx ns + ((29 * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have e : (Q : ℝ≥0∞) * noForgeryRate nx ns + ((29 * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 =
      ((Q * noForgeryRateNum nx ns + 29 * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    simp only [noForgeryRate, Nat.cast_add, Nat.cast_mul, ENNReal.add_div, mul_div_assoc]
  rw [e, sphincsMultiClosed_eq_num]
  have hle := chainCoreNum_le hQ
  split_ifs with hnx
  · split_ifs at hle
    rw [add_zero] at hle
    rw [add_zero, ENNReal.div_add_div_same, ← Nat.cast_add]
    exact ENNReal.div_le_div_right (by exact_mod_cast hle) _
  · split_ifs at hle
    rw [xmssMultiError_eq_num, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
      ← Nat.cast_add, ← Nat.cast_add]
    exact ENNReal.div_le_div_right (by exact_mod_cast hle) _

/-- **No cap**: past leanXMSS's side condition `q + 384 < 2^126`, `c q²/2^256 ≥ 1` for `c ≥ 29`. -/
theorem one_le_quad_of_large {c Q : ℕ} (hc : 29 ≤ c) (hq : ¬ Q + 384 < 2 ^ 126) :
    1 ≤ ((c * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have hQ : 2 ^ 126 - 384 ≤ Q := by omega
  have hn : 2 ^ 256 ≤ c * Q ^ 2 := by
    calc 2 ^ 256 ≤ 29 * (2 ^ 126 - 384) ^ 2 := by norm_num
      _ ≤ c * Q ^ 2 := by gcongr
  have h0 : (2 : ℝ≥0∞) ^ 256 ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ℝ≥0∞) ^ 256 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [← ENNReal.div_self h0 ht]
  exact ENNReal.div_le_div_right (by exact_mod_cast hn) _

/-! ## The decomposition -/

/-- **T5 with the cubic T3, split by scheme**, with no leanXMSS term without leanXMSS keys. -/
theorem prEvent_breaks_le_split [P : Sphincs.Params] [S : SphincsSet P] {nx ns : ℕ}
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS)
    (hq : gameQueries nx ns qH sX sS budget + 384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      aggBadError2 (gameQueries nx ns qH sX sS budget) +
        (if nx = 0 then 0 else xmssMultiError nx (gameQueries nx ns qH sX sS budget + 384)) +
        (ns : ℝ≥0∞) * (((gameQueries nx ns qH sX sS budget + 686 : ℕ) : ℝ≥0∞) /
          ((2 ^ 127 : ℕ) : ℝ≥0∞)) := by
  set Q := gameQueries nx ns qH sX sS budget
  have hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h) :=
    fun _ _ _ ↦ guestHypsM_model _
  have hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q :=
    isQueryBoundP_gameComp keygenFromSeed_isTotalQueryBound sphincsKeygenFromSeed_isTotalQueryBound
      sign_isTotalQueryBound sphincsSign_isTotalQueryBound Guest.guest fuel budget A hA.hash hA.xmss
      hA.sphincs
  set g := game Guest.guest fuel budget A
  have e : Pr{let z ← g}[Breaks z.1 z.2] ≤ Pr{let z ← g}[(AggBad2 z.2 ∨
      (z.1.accepted = true ∧ XmssRed.ForgedX z.1 ∧ ¬ AggBad2 z.2)) ∨
      (z.1.accepted = true ∧ SphincsRed.ForgedS z.1 ∧ ¬ AggBad2 z.2)] :=
    prEvent_mono_of_support _ _ _ fun z hz hb ↦ by
      by_cases hbad : AggBad2 z.2
      · exact Or.inl (Or.inl hbad)
      · rcases (forged_iff z.1).mp (forged_of_breaks2 hG hz hb hbad) with hf | hf
        · exact Or.inl (Or.inr ⟨hb.1, hf, hbad⟩)
        · exact Or.inr ⟨hb.1, hf, hbad⟩
  refine e.trans ((prEvent_or_le _ _ _).trans (add_le_add ((prEvent_or_le _ _ _).trans
    (add_le_add ?_ ?_)) ?_))
  · exact prEvent_game_aggBad2_le fuel budget A Q hQ
  · split_ifs with hnx
    · subst hnx
      exact le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun z h ↦ by
        obtain ⟨-, ⟨j, -⟩, -⟩ := h; exact j.elim0)
    · exact prEvent_forgedX_le_bound2 hG XmssSecurity.leanXmss_has_multi_user_security fuel budget
        A hQ verify_isTotalQueryBound hq
  · refine (prEvent_forgedS_le_bound2 hG (S.multi ns) keygenFromSeed_isTotalQueryBound
      sphincsKeygenFromSeed_isTotalQueryBound sign_isTotalQueryBound sphincsSign_isTotalQueryBound
      sphincsVerify_isTotalQueryBound fuel budget A hA.hash hA.xmss hA.sphincs).trans (le_of_eq ?_)
    have hm : max 1 (Q + sphincsVerifyBound) = Q + 686 :=
      max_eq_right (by unfold sphincsVerifyBound; omega)
    simp only [show nx * xmssKeygenBound + ns * sphincsKeygenBound +
      (qH + sX * xmssSignBound + sS * sphincsSignBound) + budget + sphincsVerifyBound =
        Q + sphincsVerifyBound from rfl, hm]

/-! ## The headline -/

/-- **No forgery, at any fuel and budget**: `Pr[Breaks] ≤ q · noForgeryRate n_x n_s +
30 q²/2^256`, `q` the game's hash evaluations at that budget. -/
theorem aggregate_no_forgery_linear [P : Sphincs.Params] [S : SphincsSet P] {nx ns : ℕ}
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      (gameQueries nx ns qH sX sS budget : ℝ≥0∞) * noForgeryRate nx ns +
        ((30 * gameQueries nx ns qH sX sS budget ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  set Q := gameQueries nx ns qH sX sS budget
  by_cases hq : Q + 384 < 2 ^ 126
  · calc Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2]
        ≤ aggBadError2 Q + (if nx = 0 then 0 else xmssMultiError nx (Q + 384)) +
            (ns : ℝ≥0∞) * (((Q + 686 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞)) :=
          prEvent_breaks_le_split fuel budget A hA hq
      _ = ((chainCoreNum Q : ℝ≥0∞) / 2 ^ 256 +
            (if nx = 0 then 0 else xmssMultiError nx (Q + 384)) +
            (ns : ℝ≥0∞) * (((Q + 686 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞))) + predError2 Q := by
          rw [aggBadError2_eq_core]; ring
      _ ≤ (Q * noForgeryRate nx ns + ((29 * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
            ((Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
          add_le_add (noForgery_core_le (keygens_le_gameQueries nx ns qH sX sS budget))
            (predError2_le_sq (by omega))
      _ = Q * noForgeryRate nx ns + ((30 * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [add_assoc, ENNReal.div_add_div_same, ← Nat.cast_add,
            show 29 * Q ^ 2 + Q ^ 2 = 30 * Q ^ 2 by ring]
  · exact (prEvent_le_one _).trans ((one_le_quad_of_large (by norm_num) hq).trans le_add_self)

/-- **No forgery (the headline).** For every leanSPHINCS parameter set, every numbers `n_x`, `n_s`
of honest keys, every tree size `N` and every adversary making at most `qH` hash queries, `sX`
leanXMSS and `sS` leanSPHINCS signing requests: V_I, on at most `N` nodes with the budget
`viCost N`, accepts a root statement with a forged claim of an honest key or a DA claim the
oracle's log does not back with probability at most `q · 2^-λ₁ + 30 q²/2^256`, where
`q = totalQueries n_x n_s qH sX sS N` counts every hash evaluation of the game and
`2^-λ₁ = noForgeryRate n_x n_s ≈ (n_s + 1.53)/2^127`. No other hypothesis. -/
theorem aggregate_no_forgery_final [P : Sphincs.Params] [S : SphincsSet P] {nx ns : ℕ} (N : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      (totalQueries nx ns qH sX sS N : ℝ≥0∞) * noForgeryRate nx ns +
        ((30 * totalQueries nx ns qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  aggregate_no_forgery_linear N (viCost N) A hA

/-- **The headline at `2^20 + 2^20` keys, every parameter set**: `q · 2^-106 + 30 q²/2^256`. -/
theorem aggregate_no_forgery_final_deployed [P : Sphincs.Params] [S : SphincsSet P] (N : ℕ)
    (A : GameAdversary (2 ^ 20) (2 ^ 20)) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      (totalQueries (2 ^ 20) (2 ^ 20) qH sX sS N : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 106 +
        ((30 * totalQueries (2 ^ 20) (2 ^ 20) qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine (aggregate_no_forgery_final N A hA).trans ?_
  gcongr
  exact noForgeryRate_deployed

/-- **The headline with leanXMSS keys only** (`n_x ≤ 2^21`, every parameter set):
`q · 2^-126 + 30 q²/2^256`. -/
theorem aggregate_no_forgery_final_xmss [P : Sphincs.Params] [S : SphincsSet P] {nx : ℕ}
    (hx : nx ≤ 2 ^ 21) (N : ℕ) (A : GameAdversary nx 0) {qH sX sS : ℕ}
    (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      (totalQueries nx 0 qH sX sS N : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 126 +
        ((30 * totalQueries nx 0 qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine (aggregate_no_forgery_final N A hA).trans ?_
  gcongr
  exact noForgeryRate_xmss_only hx

end LeanVM.E2E
