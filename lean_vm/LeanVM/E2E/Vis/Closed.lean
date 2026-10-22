/-
  LeanVM.E2E.Vis.Closed

  W-vis, P6b: the end theorem's error `sec0Error` in closed form, §0's `ε` of `e2e-security.md`
  as a Lean definition, the deviations between them, and their numerics.
-/

module

public import LeanVM.E2E.Vis.Bound
public import LeanVM.E2E.NoForgeryClosed

/-!
# §0's bound, the proofs' bound, and their difference (W-vis, P6b)

Pure arithmetic: nothing here depends on the proofs. The plan is `docs/roadmap/w-vis.md` §6.

**The proofs' bound.** `sec0Error Q_v Q n_x n_s q_x q_s Q_k` is the chain's error `visError`
(`Vis/Bound.lean`) plus the per-key terms `perKeyError`: one leanXMSS (resp. leanSPHINCS) reduction
per key at `Q_v + q_x` (resp. `Q_v + q_s`) hash queries, `q_x`, `q_s` a reduction's own cost beyond
the visible queries, and the key coincidences, `2n/2^128 + Q_k²/2^256` per key. The end theorem
instantiates it as `sec0ErrorGame`:
`Q_v = qH + budget`, `Q` the game's total, `q_x = 2n + c_xk + s_Xk·c_xs + c_x`,
`q_s = 2n + c_sk + s_Sk·c_ss + c_s`, `Q_k = n_x·c_xk + n_s·c_sk`, `n = n_x + n_s`.

**§0's bound.** `eps0 Q_v Q_sig′ Q_sig c n` is §0's formula written out literally, one definition per
term: `eps0KappaV` (κ_V°), `eps0KappaBatch` (κ_batch, with failBound and QV_b folded into the
game's count, W6-1), `eps0Term` (`(Q_v+1)²/2^193`), `eps0Signer` (ε_signer), `eps0Forge` (the
forgery term) and `eps0DA` (ε_DA). ε_signer's 3-collision term `(S·2^8.1)³/2^258.6` is dropped: it
is LateReveal's, which route B does not need (E2E-6), and it is no closed form over `2^256`.

**The deviations.** `delta Q_v Q n_x n_s Q_k`, one definition per term:
* `deltaHidFail`: the failure terms of the hidden queries, `(13(Q² − Q_v²) + 17(Q − Q_v))/2^256`
  (T1's `5(Q+1)`, W6's `4(Q+2)` and E5's `4(Q+1)` per query, on the hidden ones; §3 ignored
  collisions among hidden entries);
* `deltaDaVis`: E5's failure term on the visible queries, `4Q_v²/2^256`. §0's `ε_DA ≈ Q_v·14/2^192`
  drops it, and κ_V° and κ_batch cover only `9Q_v²` of the visible queries' `13Q_v²`;
* `deltaDaHid`: E5's rate on the hidden queries, `(Q − Q_v)·14/2^192` (E5 charges every query);
* `deltaFormat`: the format event, `Q(n·2^64 + 1)/2^256` (§0's Format term is `n·2^45/2^256`);
* `deltaFwd`: the other keys' two derivations, forwarded by every reduction, `n·2n/2^127`;
* `deltaKeyColl`: the key coincidences beyond §0's `n²/2^128`: the per-key event `KeyCollAt`
  (another key's parameter, or a zero parameter) is `2n/2^128` per key, `2n²/2^128` in all, and the
  repeated derivations `n·Q_k²/2^256`.

**Which §0 term absorbs what** (`sec0Error_le_eps0_add_delta`, `closedNum0_le`):

| `sec0Error` term | absorbed by |
| --- | --- |
| `Q_v·2^-128` (T1, V°) | κ_V°'s linear part `(Q_v+13213)·2^-128` |
| `Q_v·2/2^192` (W6) | κ_batch's linear part `Q_v·3/2^192` |
| `Q·14/2^192` (E5) | ε_DA `Q_v·14/2^192` and `deltaDaHid` |
| `Q_v(Q_v+1)/2^193` (T3) | `(Q_v+1)²/2^193` |
| `Q(13Q + 17)/2^256` (failures) | κ_V°'s `5(Q_v+13213)²`, κ_batch's `4Q_v(Q_v+1)`, `deltaDaVis`, `deltaHidFail` |
| `Q(n·2^64+1)/2^256` (format) | `deltaFormat` |
| `n_x(Q_v+q_x)/2^127 + n_s(Q_v+q_s)/2^127` | the forgery term `n(Q_v + Q_sig′ + c)/2^127` and `deltaFwd`, when `q_x, q_s ≤ 2n + Q_sig′ + c` |
| `n·2n/2^128` (key pairs) | ε_signer's `n²/2^128` and `deltaKeyColl` |
| `n·Q_k²/2^256` (repeated derivations) | `deltaKeyColl` |

ε_signer's other terms (`Q_v·5/2^128`, `Q_v·Q_sig/2^255`, `n·2^45/2^256`, `n(Q_v+Q_sig)/2^256`,
`n/2^128`) and κ_V°'s `13213` are not needed by route B. (For `Q_v ≤ 2^128`, `Q_v·5/2^128` alone
is above `deltaDaVis`.)

**Numerics** (`closedNum0`: `sec0Error` as one fraction over `2^256`; leanXMSS's constants
`c_xk = 13,434,881`, `c_xs = 2^33 + 40,304,605`, `c_x = 384`, `c_s = 686`, and every leanSPHINCS
set with `c_sk ≤ 2^34`, `c_ss ≤ 2^35`, which covers `full` and `pruned20`; `Q_v = qH + budget`):

| point | `sec0Error` | `delta` | today's `closedError` |
| --- | --- | --- | --- |
| lifetime: `n_x = n_s = 2^20`, `Q_v ≤ 2^64`, `s_X, s_S ≤ 2^44`, `s_Xk, s_Sk ≤ 2^24` | `≤ 2^-41` (`≈ 2^-41.97`) | `≤ 2^-84 + 2^-86 + 2^-91` (`≈ 2^-83.67`) | `≈ 2^-28.1` (`full`) |
| one slot: `s_X, s_S, s_Xk, s_Sk ≤ 2^20` | `≤ 2^-42 + 2^-51` | | `≈ 2^-43.0` |
| leanXMSS only, lifetime (`n_s = 0`), `Q_v ≤ 2^64` | `≤ 2^-42` (`≈ 2^-42.99`) | | `≈ 2^-39.0` |
| leanXMSS only, lifetime, `Q_v ≤ 2^56` | `≤ 2^-49` (`≈ 2^-49.41`) | | `≈ 2^-39.0` |

`delta ≤ 2^-84` does not hold at the lifetime point: `deltaFwd` alone is `2^-84` there
(`deltaFwd_lifetime`; `n = 2^21`, so §6's "`≈ 2^-85`" is off by a factor two), and the key pairs add
`2^-86`. The leanXMSS-only lifetime is `≈ 2^-43` at `Q_v = 2^64` (its forgery term
`2^20(Q_v + 2^57)/2^127`); `≤ 2^-49` needs `Q_v ≤ 2^56` (at `Q_v = 2^57` it is `≈ 2^-48.997`).
At one slot `sec0Error` (`≈ 2^-42`) is twice today's `closedError` (`≈ 2^-43`): the per-key hybrid
pays `n_x·Q_v/2^127` for leanXMSS, where leanXMSS's multi-user theorem pays `Q/2^127`. Over a
lifetime the visible accounting gains: today's bound is `≈ 2^-28` (its leanSPHINCS term
`n_s Q/2^127`, `Q ≈ 2^79`) and `≈ 2^-39` for leanXMSS only (T3's `Q²/2^193`).
-/

namespace LeanVM.E2E

open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.EndToEnd.Sound
open scoped ENNReal

@[expose] public section

/-! ## The proofs' bound -/

/-- Per-key forgery terms and key coincidences. `qx`, `qs`: one reduction's own cost beyond `Qv`. -/
noncomputable def perKeyError (Qv nx ns qx qs Qk : ℕ) : ℝ≥0∞ :=
  nx * (((Qv + qx : ℕ) : ℝ≥0∞) / 2 ^ 127) + ns * (((Qv + qs : ℕ) : ℝ≥0∞) / 2 ^ 127) +
    (nx + ns) * (((2 * (nx + ns) : ℕ) : ℝ≥0∞) / 2 ^ 128 + ((Qk ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- **§0's bound with the constants the proofs give.** -/
noncomputable def sec0Error (Qv Q nx ns qx qs Qk : ℕ) : ℝ≥0∞ :=
  visError Qv Q (nx + ns) + perKeyError Qv nx ns qx qs Qk

/-- **`sec0Error` at the end theorem's arguments**: `Q_v = qH + budget` visible queries, the game's
`Q` hash queries, a reduction's own costs `q_x = 2n + c_xk + s_Xk·c_xs + c_x` and
`q_s = 2n + c_sk + s_Sk·c_ss + c_s`, and the key generations' `Q_k = n_x·c_xk + n_s·c_sk`. -/
noncomputable def sec0ErrorGame (nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk : ℕ) : ℝ≥0∞ :=
  sec0Error (qH + budget) (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget) nx ns
    (2 * (nx + ns) + cxk + sXk * cxs + cx) (2 * (nx + ns) + csk + sSk * css + cs)
    (nx * cxk + ns * csk)

/-! ## §0's bound, literally -/

/-- §0's `κ_V°(Q_v) = (Q_v+13213)(2^-128 + 5(Q_v+13213)/2^256)` ("closed forms", first line). -/
noncomputable def eps0KappaV (Qv : ℕ) : ℝ≥0∞ :=
  ((Qv + 13213 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + ((5 * (Qv + 13213) : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- §0's `κ_batch(Q_v) ≤ (Q_v+QV_b)(3/|E| + failBound)`, `|E| = 2^192` ("closed forms", first
line), as `Q_v(3/2^192 + 4(Q_v+1)/2^256)`: failBound and QV_b are folded into the game's count
(W6-1). -/
noncomputable def eps0KappaBatch (Qv : ℕ) : ℝ≥0∞ :=
  (Qv : ℝ≥0∞) * (3 / 2 ^ 192 + ((4 * (Qv + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- §0's termination term `(Q_v+1)²/2^193` (the bound's first line). -/
noncomputable def eps0Term (Qv : ℕ) : ℝ≥0∞ :=
  (((Qv + 1) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 193

/-- §0's `ε_DA ≈ Q_v·14/2^192` ("closed forms", second line). -/
noncomputable def eps0DA (Qv : ℕ) : ℝ≥0∞ :=
  (Qv : ℝ≥0∞) * 14 / 2 ^ 192

/-- §0's `ε_signer` ("closed forms", `ε_signer ≤ …`): `Q_v·(3+2)/2^128` (LateReveal) +
`Q_v·Q_sig/2^255` (Hit, HiddenPredict, HiddenCollide) + `n·2^45/2^256` (Format) +
`n·Q/2^256`, `Q = Q_v + Q_sig` (GuessS) + `n/2^128` (constant-prefixed transcript starts) +
`n²/2^128` (key coincidences). The 3-collision term `(S·2^8.1)³/2^258.6` is dropped. -/
noncomputable def eps0Signer (Qv Qsig n : ℕ) : ℝ≥0∞ :=
  (Qv : ℝ≥0∞) * 5 / 2 ^ 128 + ((Qv * Qsig : ℕ) : ℝ≥0∞) / 2 ^ 255 +
    ((n * 2 ^ 45 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((n * (Qv + Qsig) : ℕ) : ℝ≥0∞) / 2 ^ 256 +
    (n : ℝ≥0∞) / 2 ^ 128 + ((n ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 128

/-- §0's forgery term `(n_x+n_s)·(Q_v + Q_sig′ + c)/2^127` (the bound's second line). -/
noncomputable def eps0Forge (Qv Qsig' c n : ℕ) : ℝ≥0∞ :=
  n * (((Qv + Qsig' + c : ℕ) : ℝ≥0∞) / 2 ^ 127)

/-- **§0's bound**, `κ_V°(Q_v) + κ_batch(Q_v) + (Q_v+1)²/2^193 + ε_signer +
(n_x+n_s)·(Q_v + Q_sig′ + c)/2^127 + ε_DA`, at `n = n_x + n_s` keys, `Q_sig′` the cost charged in
one reduction (a key generation and its signings), `Q_sig` the honest signers' total cost and `c`
the final verification's. -/
noncomputable def eps0 (Qv Qsig' Qsig c n : ℕ) : ℝ≥0∞ :=
  eps0KappaV Qv + eps0KappaBatch Qv + eps0Term Qv + eps0Signer Qv Qsig n + eps0Forge Qv Qsig' c n +
    eps0DA Qv

/-- **§0's bound at the end theorem's arguments**: `Q_sig′` the larger reduction cost
`max (c_xk + s_Xk·c_xs) (c_sk + s_Sk·c_ss)`, `Q_sig = n_x·c_xk + n_s·c_sk + s_X·c_xs + s_S·c_ss`
the signers' total and `c = max c_x c_s`. -/
noncomputable def eps0Game (nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk : ℕ) : ℝ≥0∞ :=
  eps0 (qH + budget) (max (cxk + sXk * cxs) (csk + sSk * css))
    (nx * cxk + ns * csk + (sX * cxs + sS * css)) (max cx cs) (nx + ns)

/-! ## The deviations -/

/-- **The hidden queries' failure terms**, `(13(Q² − Q_v²) + 17(Q − Q_v))/2^256`: T1's, W6's and
E5's failure rates (`5(Q+1)`, `4(Q+2)`, `4(Q+1)` per query over `2^256`) beyond the visible
queries' `13Q_v² + 17Q_v`. -/
noncomputable def deltaHidFail (Qv Q : ℕ) : ℝ≥0∞ :=
  ((13 * (Q ^ 2 - Qv ^ 2) + 17 * (Q - Qv) : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- **E5's failure term on the visible queries**, `4Q_v²/2^256`, which §0's `ε_DA ≈` drops. -/
noncomputable def deltaDaVis (Qv : ℕ) : ℝ≥0∞ :=
  ((4 * Qv ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- **DA on the hidden queries**, `(Q − Q_v)·14/2^192`: E5 charges every query its rate. -/
noncomputable def deltaDaHid (Qv Q : ℕ) : ℝ≥0∞ :=
  ((Q - Qv : ℕ) : ℝ≥0∞) * 14 / 2 ^ 192

/-- **The format event**, `Q(n·2^64 + 1)/2^256`. -/
noncomputable def deltaFormat (Q n : ℕ) : ℝ≥0∞ :=
  (Q : ℝ≥0∞) * (((n * 2 ^ 64 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- **The forwarded derivations**: every reduction forwards the other keys' two derivations,
`2n` queries, `n·2n/2^127` in all. -/
noncomputable def deltaFwd (n : ℕ) : ℝ≥0∞ :=
  n * (((2 * n : ℕ) : ℝ≥0∞) / 2 ^ 127)

/-- **The key coincidences beyond §0's `n²/2^128`**: the proofs pay `2n/2^128` per key (another
key's parameter, or a zero one), `2n²/2^128` in all, and `Q_k²/2^256` per key for a repeated
derivation. -/
noncomputable def deltaKeyColl (n Qk : ℕ) : ℝ≥0∞ :=
  ((n ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 128 + n * (((Qk ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- **The deviations of `sec0Error` from §0's bound.** -/
noncomputable def delta (Qv Q nx ns Qk : ℕ) : ℝ≥0∞ :=
  deltaHidFail Qv Q + deltaDaVis Qv + deltaDaHid Qv Q + deltaFormat Q (nx + ns) +
    deltaFwd (nx + ns) + deltaKeyColl (nx + ns) Qk

/-- **The deviations at the end theorem's arguments.** -/
noncomputable def deltaGame (nx ns cxk csk cxs css qH budget sX sS : ℕ) : ℝ≥0∞ :=
  delta (qH + budget) (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget) nx ns
    (nx * cxk + ns * csk)

/-! ## As fractions over `2^256` -/

/-- `sec0Error Qv Q nx ns qx qs Qk`, times `2^256`. -/
def closedNum0 (Qv Q nx ns qx qs Qk : ℕ) : ℕ :=
  2 ^ 128 * Qv + 2 ^ 65 * Qv + 14 * 2 ^ 64 * Q + 2 ^ 63 * (Qv * (Qv + 1)) +
    Q * (5 * (Q + 1) + 4 * (Q + 2) + 4 * (Q + 1) + ((nx + ns) * 2 ^ 64 + 1)) +
    2 ^ 129 * (nx * (Qv + qx)) + 2 ^ 129 * (ns * (Qv + qs)) +
    (nx + ns) * (2 ^ 129 * (nx + ns) + Qk ^ 2)

/-- `eps0 Qv Qsig' Qsig c n`, times `2^256`. -/
def eps0Num (Qv Qsig' Qsig c n : ℕ) : ℕ :=
  (Qv + 13213) * (2 ^ 128 + 5 * (Qv + 13213)) + Qv * (3 * 2 ^ 64 + 4 * (Qv + 1)) +
    2 ^ 63 * (Qv + 1) ^ 2 +
    (5 * 2 ^ 128 * Qv + 2 * (Qv * Qsig) + n * 2 ^ 45 + n * (Qv + Qsig) + 2 ^ 128 * n +
      2 ^ 128 * n ^ 2) +
    2 ^ 129 * (n * (Qv + Qsig' + c)) + 14 * 2 ^ 64 * Qv

/-- `delta Qv Q nx ns Qk`, times `2^256`, at `n = nx + ns`. -/
def deltaNum (Qv Q n Qk : ℕ) : ℕ :=
  (13 * (Q ^ 2 - Qv ^ 2) + 17 * (Q - Qv)) + 4 * Qv ^ 2 + 14 * 2 ^ 64 * (Q - Qv) +
    Q * (n * 2 ^ 64 + 1) + 2 ^ 129 * (n * (2 * n)) + (2 ^ 128 * n ^ 2 + n * Qk ^ 2)

/-- `2^-k` as a fraction over `2^256`. -/
theorem two_inv_pow_eq_div (k : ℕ) (hk : k ≤ 256) :
    (2 : ℝ≥0∞)⁻¹ ^ k = ((2 ^ (256 - k) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [← ENNReal.inv_pow, inv_two_pow_eq k hk, div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]

/-- **`sec0Error` as one fraction.** -/
theorem sec0Error_eq_num (Qv Q nx ns qx qs Qk : ℕ) :
    sec0Error Qv Q nx ns qx qs Qk = (closedNum0 Qv Q nx ns qx qs Qk : ℝ≥0∞) / 2 ^ 256 := by
  set I := ((2 : ℝ≥0∞) ^ 256)⁻¹
  have h128 : ((2 : ℝ≥0∞) ^ 128)⁻¹ = 2 ^ 128 * I := inv_two_pow_eq 128 (by norm_num)
  have h192 : ((2 : ℝ≥0∞) ^ 192)⁻¹ = 2 ^ 64 * I := inv_two_pow_eq 192 (by norm_num)
  have h193 : ((2 : ℝ≥0∞) ^ 193)⁻¹ = 2 ^ 63 * I := inv_two_pow_eq 193 (by norm_num)
  have h127 : ((2 : ℝ≥0∞) ^ 127)⁻¹ = 2 ^ 129 * I := inv_two_pow_eq 127 (by norm_num)
  have hs : (4 + leanVmSeeds.steps.length) * (Q + 1) = 5 * (Q + 1) := rfl
  simp only [sec0Error, visError, perKeyError, closedNum0, εLean, failBound, hs, div_eq_mul_inv,
    ← ENNReal.inv_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    h128, h192, h193, h127]
  ring

/-- **§0's bound as one fraction.** -/
theorem eps0_eq_num (Qv Qsig' Qsig c n : ℕ) :
    eps0 Qv Qsig' Qsig c n = (eps0Num Qv Qsig' Qsig c n : ℝ≥0∞) / 2 ^ 256 := by
  set I := ((2 : ℝ≥0∞) ^ 256)⁻¹
  have h128 : ((2 : ℝ≥0∞) ^ 128)⁻¹ = 2 ^ 128 * I := inv_two_pow_eq 128 (by norm_num)
  have h192 : ((2 : ℝ≥0∞) ^ 192)⁻¹ = 2 ^ 64 * I := inv_two_pow_eq 192 (by norm_num)
  have h193 : ((2 : ℝ≥0∞) ^ 193)⁻¹ = 2 ^ 63 * I := inv_two_pow_eq 193 (by norm_num)
  have h127 : ((2 : ℝ≥0∞) ^ 127)⁻¹ = 2 ^ 129 * I := inv_two_pow_eq 127 (by norm_num)
  have h255 : ((2 : ℝ≥0∞) ^ 255)⁻¹ = 2 ^ 1 * I := inv_two_pow_eq 255 (by norm_num)
  simp only [eps0, eps0KappaV, eps0KappaBatch, eps0Term, eps0DA, eps0Signer, eps0Forge, eps0Num,
    div_eq_mul_inv, ← ENNReal.inv_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, h128, h192, h193, h127, h255]
  ring

/-- **The deviations as one fraction.** -/
theorem delta_eq_num (Qv Q nx ns Qk : ℕ) :
    delta Qv Q nx ns Qk = (deltaNum Qv Q (nx + ns) Qk : ℝ≥0∞) / 2 ^ 256 := by
  set I := ((2 : ℝ≥0∞) ^ 256)⁻¹
  have h128 : ((2 : ℝ≥0∞) ^ 128)⁻¹ = 2 ^ 128 * I := inv_two_pow_eq 128 (by norm_num)
  have h192 : ((2 : ℝ≥0∞) ^ 192)⁻¹ = 2 ^ 64 * I := inv_two_pow_eq 192 (by norm_num)
  have h127 : ((2 : ℝ≥0∞) ^ 127)⁻¹ = 2 ^ 129 * I := inv_two_pow_eq 127 (by norm_num)
  simp only [delta, deltaHidFail, deltaDaVis, deltaDaHid, deltaFormat, deltaFwd, deltaKeyColl,
    deltaNum, div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, h128, h192, h127]
  ring

/-- The forwarded derivations as one fraction. -/
theorem deltaFwd_eq_num (n : ℕ) :
    deltaFwd n = ((2 ^ 129 * (n * (2 * n)) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  set I := ((2 : ℝ≥0∞) ^ 256)⁻¹
  have h127 : ((2 : ℝ≥0∞) ^ 127)⁻¹ = 2 ^ 129 * I := inv_two_pow_eq 127 (by norm_num)
  simp only [deltaFwd, div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, h127]
  ring

/-! ## `sec0Error ≤ eps0 + delta` -/

/-- **The comparison, on the numerators.** -/
theorem closedNum0_le {Qv Q nx ns qx qs Qk Qsig' Qsig c : ℕ} (hQ : Qv ≤ Q)
    (hx : qx ≤ 2 * (nx + ns) + Qsig' + c) (hs : qs ≤ 2 * (nx + ns) + Qsig' + c) :
    closedNum0 Qv Q nx ns qx qs Qk ≤
      eps0Num Qv Qsig' Qsig c (nx + ns) + deltaNum Qv Q (nx + ns) Qk := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hQ
  have e1 : (Qv + h) ^ 2 - Qv ^ 2 = 2 * Qv * h + h ^ 2 := Nat.sub_eq_of_eq_add (by ring)
  have e2 : Qv + h - Qv = h := by omega
  have hx' : nx * (Qv + qx) ≤ nx * (Qv + (2 * (nx + ns) + Qsig' + c)) := by gcongr
  have hs' : ns * (Qv + qs) ≤ ns * (Qv + (2 * (nx + ns) + Qsig' + c)) := by gcongr
  unfold closedNum0 eps0Num deltaNum
  rw [e1, e2]
  nlinarith [hx', hs', Nat.zero_le (Qv * Qsig), Nat.zero_le (nx * Qv), Nat.zero_le (ns * Qv),
    Nat.zero_le (nx * Qsig), Nat.zero_le (ns * Qsig)]

/-- **`sec0Error ≤ eps0 + delta`.** With `Q_v ≤ Q` and both reductions' own costs at most
`2n + Q_sig′ + c`, the proofs' bound is §0's plus the deviations, for every `Q_sig`. -/
theorem sec0Error_le_eps0_add_delta {Qv Q nx ns qx qs Qk Qsig' Qsig c : ℕ} (hQ : Qv ≤ Q)
    (hx : qx ≤ 2 * (nx + ns) + Qsig' + c) (hs : qs ≤ 2 * (nx + ns) + Qsig' + c) :
    sec0Error Qv Q nx ns qx qs Qk ≤ eps0 Qv Qsig' Qsig c (nx + ns) + delta Qv Q nx ns Qk := by
  rw [sec0Error_eq_num, eps0_eq_num, delta_eq_num, ENNReal.div_add_div_same, ← Nat.cast_add]
  gcongr
  exact closedNum0_le hQ hx hs

/-- **`sec0Error ≤ eps0 + delta` at the end theorem's arguments.** -/
theorem sec0ErrorGame_le (nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk : ℕ) :
    sec0ErrorGame nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk ≤
      eps0Game nx ns cxk csk cxs css cx cs qH budget sX sS sXk sSk +
        deltaGame nx ns cxk csk cxs css qH budget sX sS := by
  unfold sec0ErrorGame eps0Game deltaGame
  refine sec0Error_le_eps0_add_delta (by omega) ?_ ?_
  · have h1 := le_max_left (cxk + sXk * cxs) (csk + sSk * css)
    have h2 := le_max_left cx cs
    omega
  · have h1 := le_max_right (cxk + sXk * cxs) (csk + sSk * css)
    have h2 := le_max_right cx cs
    omega

/-! ## Numerics -/

/-- `closedNum0` grows with each argument. -/
theorem closedNum0_mono {Qv Q nx ns qx qs Qk Qv' Q' nx' ns' qx' qs' Qk' : ℕ} (hv : Qv ≤ Qv')
    (hQ : Q ≤ Q') (hx : nx ≤ nx') (hs : ns ≤ ns') (hqx : qx ≤ qx') (hqs : qs ≤ qs')
    (hk : Qk ≤ Qk') :
    closedNum0 Qv Q nx ns qx qs Qk ≤ closedNum0 Qv' Q' nx' ns' qx' qs' Qk' := by
  unfold closedNum0
  gcongr

/-- `deltaNum` is at most its form without the visible queries' discounts, which grows with each
argument. -/
theorem deltaNum_le_of_le {Qv Q n Qk Qv' Q' n' Qk' : ℕ} (hv : Qv ≤ Qv') (hQ : Q ≤ Q')
    (hn : n ≤ n') (hk : Qk ≤ Qk') :
    deltaNum Qv Q n Qk ≤ 13 * Q' ^ 2 + 17 * Q' + 4 * Qv' ^ 2 + 14 * 2 ^ 64 * Q' +
      Q' * (n' * 2 ^ 64 + 1) + 2 ^ 129 * (n' * (2 * n')) + (2 ^ 128 * n' ^ 2 + n' * Qk' ^ 2) := by
  have h1 : Q ^ 2 - Qv ^ 2 ≤ Q' ^ 2 := (Nat.sub_le _ _).trans (by gcongr)
  have h2 : Q - Qv ≤ Q' := (Nat.sub_le _ _).trans hQ
  unfold deltaNum
  gcongr

/-- A numerator of at most `M` is an error of at most `M/2^256`. -/
theorem div_two_pow_256_le {N M : ℕ} (h : N ≤ M) :
    (N : ℝ≥0∞) / 2 ^ 256 ≤ (M : ℝ≥0∞) / 2 ^ 256 := by
  gcongr

/-- **The forwarded derivations at `2^21` keys are `2^-84`**: `delta ≤ 2^-84` fails at the
lifetime point. -/
theorem deltaFwd_lifetime : deltaFwd (2 ^ 20 + 2 ^ 20) = (2 : ℝ≥0∞)⁻¹ ^ 84 := by
  rw [deltaFwd_eq_num, two_inv_pow_eq_div 84 (by norm_num)]
  norm_num

/-- The game's queries at leanXMSS's constants and `c_sk ≤ 2^34`, `c_ss ≤ 2^35`. -/
theorem gameQueries_vis_le {nx ns csk css qH budget sX sS a b : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ a) (hS : sS ≤ b) :
    nx * 13434881 + ns * csk + (qH + sX * 8630239197 + sS * css) + budget ≤
      nx * 13434881 + ns * 2 ^ 34 + (2 ^ 64 + a * 8630239197 + b * 2 ^ 35) := by
  have h1 : sX * 8630239197 ≤ a * 8630239197 := Nat.mul_le_mul_right _ hX
  have h2 : sS * css ≤ b * 2 ^ 35 := Nat.mul_le_mul hS hs
  have h3 : ns * csk ≤ ns * 2 ^ 34 := Nat.mul_le_mul_left _ hk
  linarith

/-- **The lifetime point**: `n_x = n_s = 2^20`, `qH + budget ≤ 2^64`, `s_X, s_S ≤ 2^44`,
`s_Xk, s_Sk ≤ 2^24`, leanXMSS's constants and `c_sk ≤ 2^34`, `c_ss ≤ 2^35` (the `full` set's
`15,166,603,265` and `23,756,655,991`): `sec0Error ≤ 2^-42 + 2^-47` (about `2^-41.97`). -/
theorem sec0ErrorGame_lifetime {csk css qH budget sX sS sXk sSk : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44) (hS : sS ≤ 2 ^ 44)
    (hXk : sXk ≤ 2 ^ 24) (hSk : sSk ≤ 2 ^ 24) :
    sec0ErrorGame (2 ^ 20) (2 ^ 20) 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk ≤
      (2 : ℝ≥0∞)⁻¹ ^ 42 + (2 : ℝ≥0∞)⁻¹ ^ 47 := by
  rw [sec0ErrorGame, sec0Error_eq_num, two_inv_pow_eq_div 42 (by norm_num),
    two_inv_pow_eq_div 47 (by norm_num), ENNReal.div_add_div_same, ← Nat.cast_add]
  refine div_two_pow_256_le ((closedNum0_mono (by exact hQ) (gameQueries_vis_le hk hs hQ hX hS)
    le_rfl le_rfl (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hXk) _) _)
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hk _) (Nat.mul_le_mul hSk hs)) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hk) _)).trans ?_)
  unfold closedNum0
  norm_num

/-- **The lifetime point, as asked**: `sec0Error ≤ 2^-41`. -/
theorem sec0ErrorGame_lifetime_le {csk css qH budget sX sS sXk sSk : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44) (hS : sS ≤ 2 ^ 44)
    (hXk : sXk ≤ 2 ^ 24) (hSk : sSk ≤ 2 ^ 24) :
    sec0ErrorGame (2 ^ 20) (2 ^ 20) 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk ≤
      (2 : ℝ≥0∞)⁻¹ ^ 41 := by
  refine (sec0ErrorGame_lifetime hk hs hQ hX hS hXk hSk).trans ?_
  rw [two_inv_pow_eq_div 42 (by norm_num), two_inv_pow_eq_div 47 (by norm_num),
    two_inv_pow_eq_div 41 (by norm_num), ENNReal.div_add_div_same, ← Nat.cast_add]
  exact div_two_pow_256_le (by norm_num)

/-- **The deviations at the lifetime point**: `delta ≤ 2^-84 + 2^-86 + 2^-91` (about
`2^-83.67`): the forwarded derivations' `2^-84` (`deltaFwd_lifetime`), the key pairs' `2^-86`, and
the rest. -/
theorem deltaGame_lifetime {csk css qH budget sX sS : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44) (hS : sS ≤ 2 ^ 44) :
    deltaGame (2 ^ 20) (2 ^ 20) 13434881 csk 8630239197 css qH budget sX sS ≤
      (2 : ℝ≥0∞)⁻¹ ^ 84 + (2 : ℝ≥0∞)⁻¹ ^ 86 + (2 : ℝ≥0∞)⁻¹ ^ 91 := by
  rw [deltaGame, delta_eq_num, two_inv_pow_eq_div 84 (by norm_num),
    two_inv_pow_eq_div 86 (by norm_num), two_inv_pow_eq_div 91 (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same, ← Nat.cast_add, ← Nat.cast_add]
  refine div_two_pow_256_le ((deltaNum_le_of_le (by exact hQ)
    (gameQueries_vis_le hk hs hQ hX hS) le_rfl
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hk) _)).trans ?_)
  norm_num

/-- **The deviations at the lifetime point are at most `2^-83`.** -/
theorem deltaGame_lifetime_le {csk css qH budget sX sS : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44) (hS : sS ≤ 2 ^ 44) :
    deltaGame (2 ^ 20) (2 ^ 20) 13434881 csk 8630239197 css qH budget sX sS ≤
      (2 : ℝ≥0∞)⁻¹ ^ 83 := by
  refine (deltaGame_lifetime hk hs hQ hX hS).trans ?_
  rw [two_inv_pow_eq_div 84 (by norm_num), two_inv_pow_eq_div 86 (by norm_num),
    two_inv_pow_eq_div 91 (by norm_num), two_inv_pow_eq_div 83 (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same, ← Nat.cast_add, ← Nat.cast_add]
  exact div_two_pow_256_le (by norm_num)

/-- **One slot**: `n_x = n_s = 2^20`, `qH + budget ≤ 2^64`, `s_X, s_S ≤ 2^20` (so a key's requests
`s_Xk, s_Sk ≤ 2^20`): `sec0Error ≤ 2^-42 + 2^-51`. -/
theorem sec0ErrorGame_one_slot {csk css qH budget sX sS sXk sSk : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 20) (hS : sS ≤ 2 ^ 20)
    (hXk : sXk ≤ 2 ^ 20) (hSk : sSk ≤ 2 ^ 20) :
    sec0ErrorGame (2 ^ 20) (2 ^ 20) 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk ≤
      (2 : ℝ≥0∞)⁻¹ ^ 42 + (2 : ℝ≥0∞)⁻¹ ^ 51 := by
  rw [sec0ErrorGame, sec0Error_eq_num, two_inv_pow_eq_div 42 (by norm_num),
    two_inv_pow_eq_div 51 (by norm_num), ENNReal.div_add_div_same, ← Nat.cast_add]
  refine div_two_pow_256_le ((closedNum0_mono (by exact hQ) (gameQueries_vis_le hk hs hQ hX hS)
    le_rfl le_rfl (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hXk) _) _)
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hk _) (Nat.mul_le_mul hSk hs)) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hk) _)).trans ?_)
  unfold closedNum0
  norm_num

/-- **leanXMSS only, lifetime**: `n_x = 2^20`, `n_s = 0`, `qH + budget ≤ 2^64`, `s_X, s_S ≤ 2^44`,
`s_Xk ≤ 2^24`: `sec0Error ≤ 2^-42` (about `2^-42.99`; the forgery term `2^20(Q_v + 2^57)/2^127`). -/
theorem sec0ErrorGame_lifetime_xmss {csk css qH budget sX sS sXk sSk : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 64) (hX : sX ≤ 2 ^ 44) (hS : sS ≤ 2 ^ 44)
    (hXk : sXk ≤ 2 ^ 24) :
    sec0ErrorGame (2 ^ 20) 0 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk ≤
      (2 : ℝ≥0∞)⁻¹ ^ 42 := by
  rw [sec0ErrorGame, sec0Error_eq_num, two_inv_pow_eq_div 42 (by norm_num)]
  refine div_two_pow_256_le ((closedNum0_mono (by exact hQ) (gameQueries_vis_le hk hs hQ hX hS)
    le_rfl le_rfl (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hXk) _) _)
    le_rfl le_rfl).trans ?_)
  unfold closedNum0
  norm_num

/-- **leanXMSS only, lifetime, `Q_v ≤ 2^56`**: `sec0Error ≤ 2^-49` (about `2^-49.41`; at
`Q_v = 2^57` it is about `2^-48.997`). -/
theorem sec0ErrorGame_lifetime_xmss_56 {csk css qH budget sX sS sXk sSk : ℕ} (hk : csk ≤ 2 ^ 34)
    (hs : css ≤ 2 ^ 35) (hQ : qH + budget ≤ 2 ^ 56) (hX : sX ≤ 2 ^ 44) (hS : sS ≤ 2 ^ 44)
    (hXk : sXk ≤ 2 ^ 24) :
    sec0ErrorGame (2 ^ 20) 0 13434881 csk 8630239197 css 384 686 qH budget sX sS sXk sSk ≤
      (2 : ℝ≥0∞)⁻¹ ^ 49 := by
  rw [sec0ErrorGame, sec0Error_eq_num, two_inv_pow_eq_div 49 (by norm_num)]
  refine div_two_pow_256_le ((closedNum0_mono (by exact hQ)
    (gameQueries_vis_le hk hs (hQ.trans (by norm_num)) hX hS)
    le_rfl le_rfl (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hXk) _) _)
    le_rfl le_rfl).trans ?_)
  unfold closedNum0
  norm_num

end
end LeanVM.E2E
