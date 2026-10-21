/-
  LeanVM.E2E.NoForgeryClosed

  T5 with the honest signers' and the final verifications' costs proved: the no-forgery error
  as a closed form in the adversary's queries, its signing requests, V_I's budget and the number
  of keys.
-/

module

public import LeanVM.E2E.NoForgery
public import LeanVM.E2E.Reduction.XmssBound
public import LeanVM.E2E.Reduction.SphincsBound

/-!
# No forgery (T5) in closed form

`aggregate_no_forgery` leaves the honest signers' and the final verifications' query costs as
hypotheses. They are proved (`Reduction/XmssBound.lean`, `Reduction/SphincsBound.lean`,
`Reduction/VerifyBound.lean`):

| | leanXMSS | leanSPHINCS (subtree height `b`) |
| --- | --- | --- |
| key generation | `13,434,881` | `1 + 226 · 2^b + 2 (26 - b)` |
| signature | `2^33 + 40,304,605` | `2^33 + 118,387 + Σ_{l<26} (l < b ? 226 · 2^l - 1 : 1)` |
| verification | `384` | `686` |

so the game's hash queries are `gameQueries nx ns qH sX sS budget`, and with a leanSPHINCS bound
of at most `n_s · q / 2^127` (every proved one: `Sphincs.Security.Multi.multiBound` is a minimum
with it) the error is `closedError Q nx ns`:

* the chain's bad events `Q (2^-128 + 5Q/2^256) + Q (2/2^192 + 4(Q+1)/2^256) +
  Q (14/2^192 + 4Q/2^256) + Q(Q+1)/2^193` (T1, W6, E5, T3);
* leanXMSS `(Q+384)/2^127 + n_x²/2^127 + (Q+384)²/2^252`;
* leanSPHINCS `n_s (Q+686)/2^127`

(`aggregate_no_forgery_closed`). `closedError_eq_num` writes it as one fraction
`closedNum Q nx ns / 2^256`, for numeric bounds.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open LeanVM.Protocol.EndToEnd.Sound OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-- **The game's hash queries** at the proved costs: the honest key generations, the adversary's
queries, its signing requests' signatures, and V_I's budget. -/
def gameQueries [Sphincs.Params] (nx ns qH sX sS budget : ℕ) : ℕ :=
  nx * xmssKeygenBound + ns * sphincsKeygenBound + (qH + sX * xmssSignBound + sS * sphincsSignBound) +
    budget

/-- **The no-forgery error in closed form** at `Q` hash queries, `nx` leanXMSS and `ns`
leanSPHINCS keys: the chain's bad events, leanXMSS's multi-user bound at `Q + 384` and
`ns (Q + 686) / 2^127`. -/
noncomputable def closedError (Q nx ns : ℕ) : ℝ≥0∞ :=
  (Q : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + ((5 * Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) + Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) +
      Q * (Q + 1) / 2 ^ 193 +
    (((Q + 384 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) + (nx ^ 2 : ℕ) / ((2 ^ 127 : ℕ) : ℝ≥0∞) +
      ((Q + 384) ^ 2 : ℕ) / ((2 ^ 252 : ℕ) : ℝ≥0∞)) +
    ns * (((Q + 686 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞))

/-- `closedError Q nx ns`, times `2^256`. -/
def closedNum (Q nx ns : ℕ) : ℕ :=
  2 ^ 128 * Q + 5 * Q * Q + 2 ^ 65 * Q + 4 * Q * (Q + 1) + 14 * 2 ^ 64 * Q + 4 * Q * Q +
    2 ^ 63 * (Q * (Q + 1)) + 2 ^ 129 * (Q + 384) + 2 ^ 129 * nx ^ 2 + 16 * (Q + 384) ^ 2 +
    2 ^ 129 * (ns * (Q + 686))

/-- **The no-forgery error at the proved verification costs and a leanSPHINCS bound of
`n_s · q / 2^127` is the closed form.** -/
theorem noForgeryError_eq_closed (Q nx ns : ℕ) :
    noForgeryError Q nx xmssVerifyBound sphincsVerifyBound
      (fun q ↦ ns * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞))) = closedError Q nx ns := by
  have hs : (4 + leanVmSeeds.steps.length) * Q = 5 * Q := rfl
  have hm : max 1 (Q + sphincsVerifyBound) = Q + 686 := max_eq_right (by unfold sphincsVerifyBound; omega)
  simp only [noForgeryError, aggBadError, xmssMultiError, failBound, hs, hm]
  rfl

/-- The no-forgery error is at most the closed form for every leanSPHINCS bound of at most
`n_s · q / 2^127`. -/
theorem noForgeryError_le_closed {Q nx ns : ℕ} {εs : ℕ → ℝ≥0∞}
    (hε : ∀ q, εs q ≤ ns * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞))) :
    noForgeryError Q nx xmssVerifyBound sphincsVerifyBound εs ≤ closedError Q nx ns := by
  rw [← noForgeryError_eq_closed]
  exact add_le_add_right (hε _) _

/-- `2^-k` over `2^256`. -/
theorem inv_two_pow_eq (k : ℕ) (hk : k ≤ 256) :
    ((2 : ℝ≥0∞) ^ k)⁻¹ = 2 ^ (256 - k) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have h2 : (2 : ℝ≥0∞) ^ (256 - k) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 : ℝ≥0∞) ^ (256 - k) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have h : (2 : ℝ≥0∞) ^ 256 = 2 ^ k * 2 ^ (256 - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [h, ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inr h2), mul_left_comm,
    ENNReal.mul_inv_cancel h2 h2', mul_one]

/-- **The closed form as one fraction.** -/
theorem closedError_eq_num (Q nx ns : ℕ) :
    closedError Q nx ns = (closedNum Q nx ns : ℝ≥0∞) / 2 ^ 256 := by
  set I := ((2 : ℝ≥0∞) ^ 256)⁻¹
  have h128 : ((2 : ℝ≥0∞) ^ 128)⁻¹ = 2 ^ 128 * I := inv_two_pow_eq 128 (by norm_num)
  have h192 : ((2 : ℝ≥0∞) ^ 192)⁻¹ = 2 ^ 64 * I := inv_two_pow_eq 192 (by norm_num)
  have h193 : ((2 : ℝ≥0∞) ^ 193)⁻¹ = 2 ^ 63 * I := inv_two_pow_eq 193 (by norm_num)
  have h127 : ((2 : ℝ≥0∞) ^ 127)⁻¹ = 2 ^ 129 * I := inv_two_pow_eq 127 (by norm_num)
  have h252 : ((2 : ℝ≥0∞) ^ 252)⁻¹ = 2 ^ 4 * I := inv_two_pow_eq 252 (by norm_num)
  simp only [closedError, closedNum, div_eq_mul_inv, ← ENNReal.inv_pow, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, h128, h192, h193, h127, h252]
  ring

/-- `closedNum` grows with the queries and the keys. -/
theorem closedNum_mono {Q Q' nx nx' ns ns' : ℕ} (hQ : Q ≤ Q') (hx : nx ≤ nx') (hs : ns ≤ ns') :
    closedNum Q nx ns ≤ closedNum Q' nx' ns' := by
  unfold closedNum
  gcongr

/-- A numerator of at most `2^(256 - k)` is an error of at most `2^-k`. -/
theorem closedError_le_of_num {Q nx ns k : ℕ} (hk : k ≤ 256) (h : closedNum Q nx ns ≤ 2 ^ (256 - k)) :
    closedError Q nx ns ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
  rw [closedError_eq_num, ← ENNReal.inv_pow, inv_two_pow_eq k hk, div_eq_mul_inv]
  gcongr
  exact_mod_cast h

/-- **No forgery (T5) in closed form.** For the game of the deployed guest with an adversary
making at most `qH` hash queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests: if
leanXMSS has its multi-user security, leanSPHINCS a multi-user bound `εs ≤ n_s · q / 2^127`, and
the game's queries `Q = gameQueries nx ns qH sX sS budget` satisfy `Q + 384 < 2^126`, then V_I
accepting a root statement with a forged claim of an honest key or an unbacked DA claim has
probability at most `closedError Q nx ns`. The signers' and verifications' costs are proved. -/
theorem aggregate_no_forgery_closed [Sphincs.Params] {nx ns : ℕ}
    (hxmss : LeanXmss.MultiUser.HasMultiUserSecurity)
    {εs : ℕ → ℝ≥0∞} (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs)
    (hε : ∀ q, εs q ≤ ns * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞)))
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : gameQueries nx ns qH sX sS budget + 384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      closedError (gameQueries nx ns qH sX sS budget) nx ns :=
  (aggregate_no_forgery hxmss hsph keygenFromSeed_isTotalQueryBound
    sphincsKeygenFromSeed_isTotalQueryBound sign_isTotalQueryBound sphincsSign_isTotalQueryBound
    verify_isTotalQueryBound sphincsVerify_isTotalQueryBound fuel budget A hH hX hS hq).trans
    (noForgeryError_le_closed hε)

end
end LeanVM.E2E
