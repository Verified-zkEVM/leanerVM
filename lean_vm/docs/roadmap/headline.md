# The headline statement

One no-forgery theorem, in the form

    ∀ adversary,   Pr[break] ≤ q · 2^-λ₁ + 30 q² / 2^256,

with `q` every hash evaluation of the game, `λ₁` a number of bits that depends only on the numbers
of keys, and no cap on `q` and no other side condition. It is `aggregate_no_forgery_final`
(`LeanVM/E2E/Headline.lean`, pinned in `LeanVM.lean`, tests in
`tests/LeanVMTests/E2E/Headline.lean`).

## 1. The statement

```lean
/-- A leanSPHINCS parameter set with its proved costs and multi-user bound. -/
class SphincsSet (P : Sphincs.Params) where
  keygenCost : ℕ
  signCost : ℕ
  keygen_eq : @sphincsKeygenBound P = keygenCost
  sign_eq : @sphincsSignBound P = signCost
  keygen_ge : 2 ^ 15 ≤ keygenCost
  multi : ∀ n, @Sphincs.Security.Multi.HasMultiUserBound P n
    (fun q => n * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞)))
-- instances: sphincsSetFull, sphincsSetPruned20, …14, …13, …12, …10, …8

/-- What the adversary may do. -/
structure AdvBounds (A : GameAdversary nx ns) (qH sX sS : ℕ) : Prop where
  hash : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH
  xmss : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX
  sphincs : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS

def viNodeCost : ℕ := 2 ^ 40
def viCost (N : ℕ) : ℕ := N * viNodeCost

/-- `q`: every hash evaluation of the game on trees of at most `N` nodes. -/
def totalQueries [Sphincs.Params] (nx ns qH sX sS N : ℕ) : ℕ :=
  gameQueries nx ns qH sX sS (viCost N)
-- totalQueries_eq : … = nx * 13434881 + ns * keygenCost + qH + sX * 8630239197
--                         + sS * signCost + viCost N

/-- `2^-λ₁ = (3 + 2 n_s + 1/16 + n_x/2^22) / 2^128`. -/
noncomputable def noForgeryRate (nx ns : ℕ) : ℝ≥0∞ :=
  ((2 ^ 128 * (3 + 2 * ns) + 2 ^ 124 + 2 ^ 106 * nx : ℕ) : ℝ≥0∞) / 2 ^ 256

theorem aggregate_no_forgery_final [P : Sphincs.Params] [S : SphincsSet P] {nx ns : ℕ} (N : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      (totalQueries nx ns qH sX sS N : ℝ≥0∞) * noForgeryRate nx ns +
        ((30 * totalQueries nx ns qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

theorem noForgeryRate_le (hk : k ≤ 127) (hx : nx ≤ 2 ^ 21) (hs : ns + 2 ≤ 2 ^ k) :
    noForgeryRate nx ns ≤ 2⁻¹ ^ (127 - k)
theorem aggregate_no_forgery_final_deployed :   -- 2^20 + 2^20 keys: q · 2^-106 + 30 q²/2^256
theorem aggregate_no_forgery_final_xmss :       -- n_x ≤ 2^21, n_s = 0: q · 2^-126 + 30 q²/2^256
```

One game (`game`, `fuel := N`, `budget := viCost N`), one event (`Breaks`: V_I accepts a root
statement with a forged claim of an honest key, or a DA claim the oracle's log does not back), one
theorem, seven instances.

## 2. The numbers

* **`λ₁ = 128 − log₂(3.0625 + 2 n_s + n_x/2^22) ≈ 127 − log₂(n_s + 1.53)`**, the same at every
  parameter set: V°'s `2^-128` (T1), leanXMSS's multi-user `2^-127` (free of `n_x`), leanSPHINCS's
  `n_s/2^127`. leanXMSS keys cost `n_x/2^150` per query only; the constants (`384/2^127`,
  `n_x²/2^127`, `686 n_s/2^127`) are paid by the key generations `q` counts. Proved values:

  | keys `(n_x, n_s)` | `λ₁` (exact) | stated |
  | --- | --- | --- |
  | `(2^20, 2^20)` | `106.999998` | `106` (`aggregate_no_forgery_final_deployed`) |
  | `(≤ 2^21, 0)` | `126.17` | `126` (`aggregate_no_forgery_final_xmss`) |
  | `(2^20, 2^10)` | `116.998` | `116` (`noForgeryRate_le`, `k = 11`) |
  | `n_s + 2 ≤ 2^k`, `n_x ≤ 2^21` | | `127 − k` (`noForgeryRate_le`) |

* **`30 q²/2^256`** (a q² rate of `2^-251.1`): the failures' `13` (T1 `5`, W6 `4`, E5 `4`),
  leanXMSS's multi-user `q²/2^252` (`16`), T3's `q³/(6 · 2^384) ≤ q²/2^256` (`1`, decision T3-2).
* **No side condition.** leanXMSS's multi-user theorem needs `q + 384 < 2^126`; past it
  `30 q²/2^256 ≥ 1` (`one_le_quad_of_large`). T3's cube is below the square for `q ≤ 2^128`,
  implied by the same condition.
* **Deployed points** (`full`, `2^20 + 2^20` keys):
  * one slot (`qH + viCost N ≤ 2^64`, `2^20` requests per scheme): `q ≈ 2^64.004`, bound
    `≈ 2^-43.0`, proved `≤ 2^-42` (`one_slot_full_le`, test file);
  * lifetime (`2^44` requests per scheme): `q ≈ 2^78.9`, bound `≈ 2^-28.1`. See §4.

## 3. What `q` counts

`q` is every hash evaluation of the game (E2E-1's accounting): key generations, the adversary's
queries, the requested signatures at their proved worst-case costs, and V_I's budget. It is the
count T5 already uses (`isQueryBoundP_gameComp`), it needs no visible/hidden distinction in the
statement, and its key generations pay the bound's constants.

The alternatives, in the same two-term form (`full`):

| `q` | `λ₁` at `(2^20,2^20)` / `(2^21,0)` / `(2^20,2^10)` | q² rate | one slot | lifetime |
| --- | --- | --- | --- | --- |
| **A: every hash evaluation (the headline)** | `107 / 126.2 / 117` | `2^-251` | `2^-43.0` | `2^-28.1` |
| B: adversary + V_I + one key's signer work (W-vis) | `106 / 106 / 107` | `13(n+1)²/2^256 ≈ 2^-210` | `2^-42.0` | `2^-41.97` |

(A's other points: `(2^21, 0)` one slot `2^-62.2`, lifetime `2^-49.2`; `(2^20, 2^10)` `2^-53.0`,
`2^-38.1`. B's: `2^-42.0`, `2^-42.0`; `2^-43.0`, `2^-43.0`.)

B charges `n_x + n_s` on the adversary's queries (the per-key hybrid), and with one key's signer
work in `q` the signers' total is only bounded by `n · q`, so the hidden queries' failures become
`13(n+1)² q²/2^256`. A multi-user leanXMSS reduction in the visible accounting (about 1.5–2.5k
lines) would not change that. No single `q` gets both rows' best: the bound has two resources with
different rates, the visible queries (`n_s/2^127` linear) and the honest signers' work (`2^-127`
linear, `2^-252` quadratic), and one `q` multiplies the larger rate by the larger resource.

## 4. Limits and the later steps

* **Lifetime.** `q` contains the honest signers' worst-case work (`2^33`–`2^34.5` evaluations per
  signature, its two `2^32`-attempt searches). Over `2^44` signatures that is `q ≈ 2^78.9` and the
  headline gives `≈ 2^-28` (`≈ 2^-38` with the sharp bound, §7), where the visible family
  (`aggregate_no_forgery_vis2`) proves `≈ 2^-42`. That family becomes internal in the cleanup pass
  (decided by the user); it is not a second end theorem.
* **The sharp leanSPHINCS bound** is proved (decided by the user): §7.
* **No `n_s`-free leanSPHINCS bound.** One adversary query attacks every key's few-time (FORS)
  layer, so a multi-target attack wins with about `n_s · β · q/2^128`; the sharp bound has that
  shape. Charging each key its attributed calls could only remove `n_s` from the honest signers'
  work (their inputs carry the key's prefix), which a single `q` cannot separate. With A's `q`,
  `λ₁ ≈ 128 − log₂(4.75 + β n_s)` is the ceiling (`125.7` only at `n_s ≈ 1`).
* **`viCost`.** `viNodeCost = 2^40` is a definition. No-forgery holds for every budget, so its value
  only enters `q`; that the honest V_I stays within `viCost N` (a per-node cost bound) is a
  completeness obligation, not proved yet. With `N = 2^20` nodes it adds `2^60` to `q`.

## 5. Proof

From T5 with the cubic T3 (`NoForgery2.lean`), leanXMSS's proved multi-user security
(`XmssSecurity.leanXmss_has_multi_user_security`), leanSPHINCS's `requestedMultiUser` and the proved
costs, plus arithmetic, all in `Headline.lean`:

| lemma | content |
| --- | --- |
| `prEvent_breaks_le_split` | T5's decomposition (`prEvent_game_aggBad2_le`, `forged_of_breaks2`, `prEvent_forgedX_le_bound2`, `prEvent_forgedS_le_bound2`), with no leanXMSS term when `n_x = 0` |
| `aggBadError2_eq_core`, `xmssMultiError_eq_num`, `sphincsMultiClosed_eq_num` | each term over `2^256`, T3 apart |
| `keygens_le_gameQueries` | `n_x 2^23 + n_s 2^15 ≤ q` |
| `chainCoreNum_le`, `noForgery_core_le` | everything but T3 is `q · rate + 29 q²/2^256` |
| `one_le_quad_of_large` | past `q + 384 ≥ 2^126`, `c q²/2^256 ≥ 1` (`c ≥ 29`) |
| `aggregate_no_forgery_linear` | the headline at any fuel and budget (T3 by `predError2_le_sq`) |
| `aggregate_no_forgery_final` | at `fuel := N`, `budget := viCost N` |
| `noForgeryRate_le`, `noForgeryRate_deployed`, `noForgeryRate_xmss_only` | `λ₁` |
| `totalQueries_eq` | `q` at the proved costs |

## 6. The cleanup pass (not done yet)

The older end theorems stay until one cleanup pass. Then: `aggregate_no_forgery`,
`aggregate_no_forgery2`, `…_closed`, `noForgeryError`, `closedError`, `aggBadError` become internal
lemmas; the per-set `aggregate_no_forgery_deployed_*`, `…2_deployed_*`, `…_sharp`, `…_one_slot_*`
are replaced by the instances; the visible family (`gameRec`, `BreaksVis`, `sec0Error*`, `eps0`,
`delta`, `visError*`, `aggregate_no_forgery_vis*`) becomes internal (decided by the user); `aggregate_knowledge_cache`
stays internal (its DA half is the event's DA clause). Optional: a knowledge companion
`Pr[accepted ∧ ¬ ClaimsKnown] ≤ aggBadError2 q` (`λ ≈ 128`, no multi-user loss, about 40 lines);
`BreaksVis` (DA backed by V_I's own trace) at these numbers (about 300–600 lines).

## 7. The sharp headline

`aggregate_no_forgery_final_sharp` (`LeanVM/E2E/HeadlineSharp.lean`, tests in
`tests/LeanVMTests/E2E/HeadlineSharp.lean`): the headline with leanSPHINCS's per-key multi-user
bound `Multi.multiBound` (`Sphincs.Lifetimes.requestedMultiUserKey`) in place of `n_s q/2^127`.

```lean
class SphincsSetSharp (P : Sphincs.Params) extends SphincsSet P where
  sharpBound : ℕ → ℕ → ℝ≥0∞
  sharp : ∀ n, @Sphincs.Security.Multi.HasMultiUserBound P n (sharpBound n)
  linA : ℕ      -- the linear numerator free of n_s (over 2^256), ≈ 1.75 · 2^128 at full
  linB : ℕ      -- per key, ≈ 0.0020 · 2^128 at full
  quadD : ℕ     -- the quadratic coefficient per key
  sharp_le : ∀ n Q, 1 ≤ n → n * keygenCost ≤ Q →
    sharpBound n (Q + 686) ≤ ((Q * (linA + linB * n + 4 * n ^ 2) + quadD * n * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256
-- instances: sphincsSetSharpFull, …Pruned20, …14, …13, …12, …10, …8

noncomputable def noForgeryRateSharp [P : Sphincs.Params] [S : SphincsSetSharp P] (nx ns : ℕ) : ℝ≥0∞ :=
  ((noForgeryRateNum nx 0 + S.linA + S.linB * ns + 4 * ns ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

theorem aggregate_no_forgery_final_sharp [P : Sphincs.Params] [S : SphincsSetSharp P] {nx ns : ℕ}
    (N : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      (totalQueries nx ns qH sX sS N : ℝ≥0∞) * noForgeryRateSharp nx ns +
        (((30 + S.quadD * ns) * totalQueries nx ns qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

theorem aggregate_no_forgery_final_sharp_deployed …   -- full, pruned20 (sharp_full_deployed, …):
  -- Pr[Breaks] ≤ q · 2^-116 + 2^34 q²/2^256 at 2^20 + 2^20 keys
```

**The numbers** (exact `λ₁` from the instances' constants; `D` per key):

| set | `λ₁ (2^20, 2^20)` | `λ₁ (2^20, 2^10)` | `λ₁ (·, 1)` | `β` | `D` |
| --- | --- | --- | --- | --- | --- |
| `full` | `116.97` (stated `116`) | `125.17` | `125.73` | `0.00199` | `10,857 = 2^13.41` |
| `pruned20` | `116.12` (stated `116`) | `124.85` | `125.70` | `0.00359` | `2^12.25` |
| `pruned14` | `115.13` | `124.35` | `125.67` | `0.00713` | `2^11.17` |
| `pruned13` | `115.00` | `124.27` | `125.67` | `0.00783` | `2^11.02` |
| `pruned12` | `114.85` | `124.17` | `125.66` | `0.00868` | `2^10.88` |
| `pruned10` | `114.58` | `124.00` | `125.66` | `0.01045` | `2^10.61` |
| `pruned8` | `114.41` (stated `114`, test) | `123.88` | `125.65` | `0.01179` | `2^10.39` |

`2^-λ₁ = (3 · 2^128 + 2^124 + 2^106 n_x + linA + linB n_s + 4 n_s²)/2^256 ≈ (4.81 + β n_s)/2^128`.
At `full`, `2^20 + 2^20` keys: one slot `≈ 2^-53.0` (`q ≈ 2^64.004`), lifetime `≈ 2^-38.1`
(`q ≈ 2^78.9`); the quadratic term is `≈ 2^-94.6` and `≈ 2^-64.8` there.

**The quadratic term `(30 + D n_s) q²/2^256`, honestly.** `multiSmall` itself has a per-key
quadratic term `4(1 + Cq) q²/2^256` (`1,348 ≈ 2^10.4` at `full`: the near certificate's
`ν (M − kc)² c`, and `ν C(M−kc, 2) rateS`). But `multiSmall` holds only up to the certificates'
budget, `2(q + 307) − keygenCost ≤ qh` (`qh ≈ 2^117.6` at `full`, `2^118.75` at `pruned20`);
beyond it `multiBound` is `n q/2^127`, which is not below the sharp linear term. It is below
`D n q²/2^256` once `D q ≥ 2^129`, so `D = ⌈2^131/(qh + kc − 1985)⌉` (`2^13.41` at `full`,
`2^12.25` at `pruned20`), above the per-key term at every set. At `n_s = 2^20`:
`30 + D 2^20 ≤ 2^34`, a q² rate of `2^-222` (`full`). The flag stands: this is the only q² rate
worse than `2^-250`, and it is what the sharp `λ₁` costs.

**The evaluation.** The certificates' constants (`small_bXX.B`, `near_bXX.En`) are equalities proved
by `decide +kernel` (`sharpB_b26`, `sharpEn_b26`, …), about ten seconds each; the module builds in
about one minute (9 GB). `ρ` is a literal, `c` follows by `norm_num`. The arithmetic
(`multiSmall_le_num`, `multiBound_le_sharp`) bounds each factor of `multiSmall`: the main factor
`ρ/2^128/(1 − Mρ/2^128) ≤ Xa/2^256` (`Xa = ⌈F X/(F−1)⌉`, `F` the largest power of two with
`(qh + kc) X F ≤ 2^256`, so `1/F ≤ 2^-6` of slack), `pairChance = (2^128 + 2)/2^256`,
`rateS ≤ 2/2^128`, and the per-key rest; the per-key constants are paid by the key generations
(`n · keygenCost ≤ q`).

