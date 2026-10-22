import LeanVM.E2E.HeadlineSharp

/-!
# Unforgeability in one term: `Pr[break] ≤ (n_s + n_x/2^23 + 4) · q / 2^127`

The headline of `LeanVM/E2E/Main.lean` (decided by the user, `e2e-security.md` §7, E2E-14).

* **One resource.** `HashEvals A N q`: the game against `A` on trees of at most `N` nodes makes at
  most `q` hash evaluations, the honest key generations, the adversary's queries, the signatures
  it requests at their proved worst-case costs and V_I's budget `viCost N` counted
  (`totalQueries_eq`); `q` bounds the game's hash queries (`hashEvals_isQueryBound`).
* **One term.** `aggregate_no_forgery_final`'s `q · noForgeryRate n_x n_s + 30 q²/2^256` is at
  most `(n_s + n_x/2^23 + 4) · q / 2^127` for every `q`: past `q = 2^125` the right side is at
  least `1`, below it `30 q²/2^256 < 1.9 q/2^127` (`unforgeable_le`).
* **The sharp form.** With leanSPHINCS's per-key multi-user bound the quadratic term does not fold
  (`(30 + D n_s) q²/2^256`, `D n_s ≈ 2^34`); `aggregate_unforgeable_sharp` keeps both terms:
  `q / 2^116 + 2^34 q²/2^256` at `2^20 + 2^20` keys.
-/

namespace LeanVM.E2E

open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Rom OracleSpec OracleComp
open scoped ENNReal

/-- **The game against `A` on at most `N` nodes makes at most `q` hash evaluations**: `A` makes at
most `qH` hash queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests (`AdvBounds`), and
`totalQueries n_x n_s qH sX sS N ≤ q`. -/
def HashEvals [Sphincs.Params] {nx ns : ℕ} (A : GameAdversary nx ns) (N q : ℕ) : Prop :=
  ∃ qH sX sS, AdvBounds A qH sX sS ∧ totalQueries nx ns qH sX sS N ≤ q

/-- **`q` bounds the game's hash queries**, the signers' and V_I's included. -/
theorem hashEvals_isQueryBound [Sphincs.Params] {nx ns N q : ℕ} {A : GameAdversary nx ns}
    (h : HashEvals A N q) : IsQueryBoundP (gameComp Guest.guest N (viCost N) A) IsHash q := by
  obtain ⟨qH, sX, sS, hA, hq⟩ := h
  exact (isQueryBoundP_gameComp keygenFromSeed_isTotalQueryBound
    sphincsKeygenFromSeed_isTotalQueryBound sign_isTotalQueryBound sphincsSign_isTotalQueryBound
    Guest.guest N (viCost N) A hA.hash hA.xmss hA.sphincs).mono hq

/-- The one-term bound as a fraction over `2^256`. -/
theorem unforgeableBound_eq (nx ns q : ℕ) :
    ((ns : ℝ≥0∞) + nx / 2 ^ 23 + 4) * q / 2 ^ 127 =
      ((q * (2 ^ 129 * ns + 2 ^ 106 * nx + 2 ^ 131) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have h0 : ∀ k : ℕ, (2 : ℝ≥0∞) ^ k ≠ 0 := fun _ ↦ pow_ne_zero _ two_ne_zero
  have ht : ∀ k : ℕ, (2 : ℝ≥0∞) ^ k ≠ ⊤ := fun _ ↦ ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hx : (nx : ℝ≥0∞) / 2 ^ 23 * 2 ^ 129 = nx * 2 ^ 106 := by
    rw [show (2 : ℝ≥0∞) ^ 129 = 2 ^ 23 * 2 ^ 106 by rw [← pow_add], ← mul_assoc,
      ENNReal.div_mul_cancel (h0 23) (ht 23)]
  rw [show (2 : ℝ≥0∞) ^ 256 = 2 ^ 127 * 2 ^ 129 by rw [← pow_add],
    ← ENNReal.mul_div_mul_right _ _ (h0 129) (ht 129)]
  congr 1
  calc ((ns : ℝ≥0∞) + nx / 2 ^ 23 + 4) * q * 2 ^ 129
      = q * (2 ^ 129 * ns + nx / 2 ^ 23 * 2 ^ 129 + 2 ^ 131) := by ring
    _ = _ := by rw [hx]; push_cast; ring

/-- **The two terms fit in one**: `q · noForgeryRate n_x n_s + 30 q²/2^256 ≤
(n_s + n_x/2^23 + 4) · q / 2^127` whenever the right side is below `1`. -/
theorem unforgeable_le {nx ns q : ℕ} (hq : q * (2 ^ 129 * ns + 2 ^ 106 * nx + 2 ^ 131) < 2 ^ 256) :
    (q : ℝ≥0∞) * noForgeryRate nx ns + ((30 * q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((ns : ℝ≥0∞) + nx / 2 ^ 23 + 4) * q / 2 ^ 127 := by
  have hq' : q < 2 ^ 125 := by
    by_contra h
    have : 2 ^ 125 * 2 ^ 131 ≤ q * (2 ^ 129 * ns + 2 ^ 106 * nx + 2 ^ 131) :=
      Nat.mul_le_mul (by omega) (by omega)
    norm_num at this hq
    omega
  have hn : q * noForgeryRateNum nx ns + 30 * q ^ 2 ≤
      q * (2 ^ 129 * ns + 2 ^ 106 * nx + 2 ^ 131) := by
    rw [show q * noForgeryRateNum nx ns + 30 * q ^ 2 = q * (noForgeryRateNum nx ns + 30 * q) by
      ring]
    refine Nat.mul_le_mul_left _ ?_
    unfold noForgeryRateNum
    omega
  rw [unforgeableBound_eq, noForgeryRate, ← mul_div_assoc, ENNReal.div_add_div_same]
  gcongr
  exact_mod_cast hn

/-- **Unforgeability.** For every proved leanSPHINCS parameter set, every numbers `n_x`, `n_s` of
honest keys, every tree size `N` and every adversary `A` whose game makes at most `q` hash
evaluations: `V_I` accepts a forged claim of an honest key or an unbacked DA claim with
probability at most `(n_s + n_x/2^23 + 4) · q / 2^127`. -/
theorem aggregate_unforgeable [P : Sphincs.Params] [S : SphincsSet P] {nx ns N q : ℕ}
    (A : GameAdversary nx ns) (hq : HashEvals A N q) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      ((ns : ℝ≥0∞) + nx / 2 ^ 23 + 4) * q / 2 ^ 127 := by
  obtain ⟨qH, sX, sS, hA, hQ⟩ := hq
  by_cases hl : q * (2 ^ 129 * ns + 2 ^ 106 * nx + 2 ^ 131) < 2 ^ 256
  · refine (aggregate_no_forgery_final N A hA).trans (le_trans ?_ (unforgeable_le hl))
    exact add_le_add (mul_le_mul_left (Nat.cast_le.mpr hQ) _)
      (ENNReal.div_le_div_right
        (Nat.cast_le.mpr (Nat.mul_le_mul_left 30 (Nat.pow_le_pow_left hQ 2))) _)
  · refine (prEvent_le_one _).trans ?_
    rw [unforgeableBound_eq]
    have h0 : (2 : ℝ≥0∞) ^ 256 ≠ 0 := pow_ne_zero _ two_ne_zero
    have ht : (2 : ℝ≥0∞) ^ 256 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    rw [← ENNReal.div_self h0 ht]
    exact ENNReal.div_le_div_right (by exact_mod_cast not_lt.mp hl) _

/-- `q · 2^k / 2^(m + k) = q / 2^m`. -/
theorem cast_mul_two_pow_div (q m k : ℕ) :
    ((q * 2 ^ k : ℕ) : ℝ≥0∞) / 2 ^ (m + k) = q / 2 ^ m := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add,
    ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]

/-- **`2^20 + 2^20` keys: `q / 2^106`**, every parameter set. -/
theorem aggregate_unforgeable_deployed [P : Sphincs.Params] [S : SphincsSet P] {N q : ℕ}
    (A : GameAdversary (2 ^ 20) (2 ^ 20)) (hq : HashEvals A N q) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤ q / 2 ^ 106 := by
  refine (aggregate_unforgeable A hq).trans ?_
  rw [unforgeableBound_eq, show (256 : ℕ) = 106 + 150 from rfl, ← cast_mul_two_pow_div q 106 150]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (by norm_num))) _

/-- **leanXMSS keys only (`n_x ≤ 2^21`): `q / 2^124`** (`λ ≈ 124.9`), every parameter set. -/
theorem aggregate_unforgeable_xmss [P : Sphincs.Params] [S : SphincsSet P] {nx N q : ℕ}
    (hx : nx ≤ 2 ^ 21)
    (A : GameAdversary nx 0) (hq : HashEvals A N q) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤ q / 2 ^ 124 := by
  refine (aggregate_unforgeable A hq).trans ?_
  rw [unforgeableBound_eq, show (256 : ℕ) = 124 + 132 from rfl, ← cast_mul_two_pow_div q 124 132]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (by omega))) _

/-- **Unforgeability with leanSPHINCS's sharp per-key bound** (`SphincsSetSharp`, every proved
set), for every adversary whose game makes at most `q` hash evaluations:
`q · noForgeryRateSharp n_x n_s + (30 + D n_s) q²/2^256`. -/
theorem aggregate_unforgeable_sharp [P : Sphincs.Params] [S : SphincsSetSharp P] {nx ns N q : ℕ}
    (A : GameAdversary nx ns) (hq : HashEvals A N q) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      (q : ℝ≥0∞) * noForgeryRateSharp nx ns +
        (((30 + S.quadD * ns) * q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨qH, sX, sS, hA, hQ⟩ := hq
  exact (aggregate_no_forgery_final_sharp N A hA).trans
    (add_le_add (mul_le_mul_left (Nat.cast_le.mpr hQ) _) (ENNReal.div_le_div_right
      (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ 2))) _))

/-- **The sharp form at the deployed sets** `full` and `pruned20` (`hP` is `sharp_full_deployed`
or `sharp_pruned20_deployed`), `2^20 + 2^20` keys: `q / 2^116 + 2^34 q²/2^256`. -/
theorem aggregate_unforgeable_sharp_deployed [P : Sphincs.Params] [S : SphincsSetSharp P]
    (hP : noForgeryRateSharp (2 ^ 20) (2 ^ 20) ≤ (2 : ℝ≥0∞)⁻¹ ^ 116 ∧
      30 + S.quadD * 2 ^ 20 ≤ 2 ^ 34)
    {N q : ℕ} (A : GameAdversary (2 ^ 20) (2 ^ 20)) (hq : HashEvals A N q) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      q / 2 ^ 116 + ((2 ^ 34 * q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨qH, sX, sS, hA, hQ⟩ := hq
  refine (aggregate_no_forgery_final_sharp_deployed hP N A hA).trans (add_le_add ?_ ?_)
  · rw [div_eq_mul_inv, ← ENNReal.inv_pow]
    exact mul_le_mul_left (Nat.cast_le.mpr hQ) _
  · exact ENNReal.div_le_div_right
      (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ 2))) _

end LeanVM.E2E
