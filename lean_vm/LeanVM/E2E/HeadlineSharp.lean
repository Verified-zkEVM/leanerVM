import LeanVM.E2E.Headline
import Sphincs.LifetimesMultiKey

/-!
# The headline with leanSPHINCS's sharp multi-user bound

`aggregate_no_forgery_final_sharp`: the headline (`Headline.lean`) with leanSPHINCS's per-key
multi-user bound `Multi.multiBound` (`Sphincs.Lifetimes.requestedMultiUserKey`) in place of
`n q/2^127`:

    Pr[Breaks] ≤ q · noForgeryRateSharp n_x n_s + (30 + D · n_s) q² / 2^256.

* **The linear rate** `noForgeryRateSharp n_x n_s = (noForgeryRateNum n_x 0 + linA + linB n_s +
  4 n_s²)/2^256`: T1 and leanXMSS as in the headline, leanSPHINCS's `linA ≈ ρ 2^128` (free of
  `n_s`, `ρ ≈ 1.75` at `full`) and `linB ≈ 2 B 2^256` per key (`β = linB/2^128 ≈ 0.0020` at `full`,
  `0.0036` at `pruned20`). `λ₁ = 116` at `2^20 + 2^20` keys for `full` (exactly `116.97`) and
  `pruned20` (`116.12`); `114`–`115` at the other sets.
* **The quadratic term** `(30 + D n_s) q²/2^256`: the headline's `30` and `D` per leanSPHINCS key.
  `D` is set by the certificates' budget: the per-key bound `multiSmall` holds up to
  `2(q + 307) − keygenCost ≤ qh` (`qh ≈ 2^117.6` at `full`), and beyond it only `n q/2^127`, which
  is below `D n q²/2^256` once `D q ≥ 2^129`. So `D = ⌈2^131/(qh + keygenCost − 1985)⌉`
  (`2^13.41` at `full`, `2^12.25` at `pruned20`), above the per-key quadratic term of `multiSmall`
  itself (`4(1 + Cq)`, `2^10.4` at `full`). At `2^20` keys, `(30 + D 2^20) ≤ 2^34`.
* The constants of the certificates (`small_bXX.B`, `near_bXX.En`) are evaluated by the kernel
  (`decide +kernel`, about ten seconds each).

`SphincsSetSharp` extends `SphincsSet` with the sharp bound and its constants; `full`, `pruned20`,
`pruned14`, `pruned13`, `pruned12`, `pruned10` and `pruned8` are instances.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open LeanVM.Protocol.EndToEnd.Sound OracleSpec OracleComp
open scoped ENNReal

/-! ## Arithmetic in `ℝ≥0∞` -/

/-- A rational below `a / 2^k` is, as a real, below `a / 2^k` in `ℝ≥0∞`. -/
theorem ofReal_rat_le_div {r : ℚ} {a k : ℕ} (h : r ≤ (a : ℚ) / 2 ^ k) :
    ENNReal.ofReal (r : ℝ) ≤ (a : ℝ≥0∞) / 2 ^ k := by
  have h' : (r : ℝ) ≤ (a : ℝ) / 2 ^ k := by
    have := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at this
    exact this
  refine (ENNReal.ofReal_le_ofReal h').trans (le_of_eq ?_)
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow
    (by norm_num), ENNReal.ofReal_ofNat]

/-- `(a/2^i)(b/2^j) = ab/2^(i+j)`. -/
theorem natDiv_mul_natDiv (a b i j : ℕ) :
    (a : ℝ≥0∞) / 2 ^ i * ((b : ℝ≥0∞) / 2 ^ j) = ((a * b : ℕ) : ℝ≥0∞) / 2 ^ (i + j) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, pow_add,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), Nat.cast_mul]
  ring

/-- `(1 − a)⁻¹ ≤ F/(F − 1)` once `a F ≤ 1`. -/
theorem ennInv_one_sub_le {a : ℝ≥0∞} {F : ℕ} (hF : 2 ≤ F) (ha : a * F ≤ 1) :
    (1 - a)⁻¹ ≤ (F : ℝ≥0∞) / ((F - 1 : ℕ) : ℝ≥0∞) := by
  have hF0 : (F : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show F ≠ 0 by omega)
  have hFt : (F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top F
  have hG0 : ((F - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show F - 1 ≠ 0 by omega)
  have haF : a ≤ 1 / F := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hF0) (Or.inl hFt)]
    exact ha
  have h1F : (1 : ℝ≥0∞) + ((F - 1 : ℕ) : ℝ≥0∞) = (F : ℝ≥0∞) := by
    exact_mod_cast (show 1 + (F - 1) = F by omega)
  have hsum : 1 / (F : ℝ≥0∞) + ((F - 1 : ℕ) : ℝ≥0∞) / F = 1 := by
    rw [ENNReal.div_add_div_same, h1F, ENNReal.div_self hF0 hFt]
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top hF0) haF
  have hle : ((F - 1 : ℕ) : ℝ≥0∞) / F ≤ 1 - a := by
    refine ENNReal.le_sub_of_add_le_left hat ?_
    calc a + ((F - 1 : ℕ) : ℝ≥0∞) / F ≤ 1 / F + ((F - 1 : ℕ) : ℝ≥0∞) / F := add_le_add haF le_rfl
      _ = 1 := hsum
  calc (1 - a)⁻¹ ≤ (((F - 1 : ℕ) : ℝ≥0∞) / F)⁻¹ := ENNReal.inv_le_inv.mpr hle
    _ = (F : ℝ≥0∞) / ((F - 1 : ℕ) : ℝ≥0∞) := ENNReal.inv_div (Or.inl hFt) (Or.inl hF0)

/-! ## `multiSmall` and `multiBound` as fractions over `2^256` -/

section Generic

open Sphincs.Security Sphincs.Security.Multi Sphincs.Security.ForsPotential

variable [Sphincs.Params]

omit [Sphincs.Params] in
/-- leanSPHINCS's chance of two keys sharing a parameter: `(2^128 + 2)/2^256`. -/
theorem sphincsPairChance_eq : pairChance = ((2 ^ 128 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have c1 : Fintype.card Sphincs.MasterSeed = 2 ^ 256 := by simp
  have c2 : Fintype.card Sphincs.HashOutput = 2 ^ 256 := by simp [Sphincs.hashOutputBits]
  have c3 : Fintype.card Sphincs.Digest = 2 ^ 128 := by simp [Sphincs.digestBits]
  rw [pairChance, c1, c2, c3]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add]
  rw [inv_two_pow_eq 128 (by norm_num), show 256 - 128 = 128 from rfl]
  generalize ((2 : ℝ≥0∞) ^ 256) = T
  rw [div_eq_mul_inv]
  ring

/-- `rateS ≤ 2/2^128`. -/
theorem sphincsRateS_le : rateS ≤ (2 : ℝ≥0∞) / 2 ^ 128 := by
  have c3 : Fintype.card Sphincs.Randomness = 2 ^ 128 := by simp [Sphincs.digestBits]
  have h3 : (Fintype.card Sphincs.Randomness : ℝ≥0∞)⁻¹ = (2 ^ 128)⁻¹ := by
    rw [c3, Nat.cast_pow, Nat.cast_ofNat]
  rw [rateS, h3, div_eq_mul_inv, mul_comm (2 : ℝ≥0∞)]
  gcongr
  calc (1 - ForestPrice.landing) + 1 ≤ 1 + 1 := add_le_add tsub_le_self le_rfl
    _ = 2 := one_add_one_eq_two

omit [Sphincs.Params] in
/-- The small route's main factor: `ρ/2^128/(1 − Mρ/2^128) ≤ Xa/2^256`. -/
theorem sphincsMulti_main_le {M X F Xa : ℕ} {ρ : ℝ}
    (hX : ENNReal.ofReal (ρ / 2 ^ 128) ≤ (X : ℝ≥0∞) / 2 ^ 256) (hF : 2 ≤ F)
    (hMX : M * X * F ≤ 2 ^ 256) (hXa : F * X ≤ (F - 1) * Xa) :
    ENNReal.ofReal (ρ / 2 ^ 128) * (1 - (M : ℝ≥0∞) * ENNReal.ofReal (ρ / 2 ^ 128))⁻¹ ≤
      (Xa : ℝ≥0∞) / 2 ^ 256 := by
  set x := ENNReal.ofReal (ρ / 2 ^ 128)
  have hax : (M : ℝ≥0∞) * x * F ≤ 1 := by
    calc (M : ℝ≥0∞) * x * F ≤ (M : ℝ≥0∞) * ((X : ℝ≥0∞) / 2 ^ 256) * F := by gcongr
      _ = ((M * X * F : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul, Nat.cast_mul]; ring
      _ ≤ ((2 ^ 256 : ℕ) : ℝ≥0∞) / 2 ^ 256 := ENNReal.div_le_div_right (by exact_mod_cast hMX) _
      _ = 1 := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
          exact ENNReal.div_self (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hG0 : ((F - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show F - 1 ≠ 0 by omega)
  have hGt : ((F - 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc x * (1 - (M : ℝ≥0∞) * x)⁻¹ ≤ (X : ℝ≥0∞) / 2 ^ 256 * ((F : ℝ≥0∞) / ((F - 1 : ℕ) : ℝ≥0∞)) :=
        mul_le_mul' hX (ennInv_one_sub_le hF hax)
    _ = ((X * F : ℕ) : ℝ≥0∞) / ((F - 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
        rw [Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring
    _ ≤ (Xa : ℝ≥0∞) / 2 ^ 256 := by
        refine ENNReal.div_le_div_right ?_ _
        rw [ENNReal.div_le_iff hG0 hGt]
        rw [show (Xa : ℝ≥0∞) * ((F - 1 : ℕ) : ℝ≥0∞) = (((F - 1) * Xa : ℕ) : ℝ≥0∞) by push_cast; ring]
        exact_mod_cast (show X * F ≤ (F - 1) * Xa by rw [mul_comm]; exact hXa)

omit [Sphincs.Params] in
/-- The small route's sum: at most `q + q n² (2^128 + 2)/2^256 + 315 n`, for `M ≤ 2^128`. -/
theorem sphincsMulti_sum_le {n q : ℕ} (hM : 2 * (q + 307) ≤ 2 ^ 128) :
    (q : ℝ≥0∞) * (1 + (n * n : ℝ≥0∞) * pairChance) +
        (n : ℝ≥0∞) * (309 + 3 * (((2 * (q + 307) : ℕ) : ℝ≥0∞) * ((2 * (q + 307) : ℕ) : ℝ≥0∞) /
          2 ^ 256) + ((q + 307 : ℕ) : ℝ≥0∞) * (3 * (((2 * (q + 307) : ℕ) : ℝ≥0∞) / 2 ^ 256))) ≤
      (q : ℝ≥0∞) + (q * n ^ 2 : ℕ) * (((2 ^ 128 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) + ((315 * n : ℕ) : ℝ≥0∞) := by
  have h0 : (2 : ℝ≥0∞) ^ 256 ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ℝ≥0∞) ^ 256 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hA : (((2 * (q + 307) : ℕ) : ℝ≥0∞) * ((2 * (q + 307) : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤ 1 := by
    rw [ENNReal.div_le_iff h0 ht, one_mul, ← Nat.cast_mul]
    have : 2 * (q + 307) * (2 * (q + 307)) ≤ 2 ^ 128 * 2 ^ 128 := Nat.mul_le_mul hM hM
    exact_mod_cast this.trans (by norm_num)
  have hB : ((q + 307 : ℕ) : ℝ≥0∞) * (3 * (((2 * (q + 307) : ℕ) : ℝ≥0∞) / 2 ^ 256)) ≤ 3 := by
    rw [mul_left_comm, ← mul_div_assoc, ← Nat.cast_mul]
    refine (mul_le_mul' (le_refl (3 : ℝ≥0∞)) (ENNReal.div_le_of_le_mul ?_)).trans
      (le_of_eq (mul_one _))
    rw [one_mul]
    have : (q + 307) * (2 * (q + 307)) ≤ 2 ^ 256 := by
      have h1 : q + 307 ≤ 2 ^ 128 := by omega
      calc (q + 307) * (2 * (q + 307)) ≤ 2 ^ 128 * 2 ^ 128 := Nat.mul_le_mul h1 hM
        _ = 2 ^ 256 := by norm_num
    exact_mod_cast this
  rw [sphincsPairChance_eq]
  calc (q : ℝ≥0∞) * (1 + (n * n : ℝ≥0∞) * (((2 ^ 128 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 256)) +
        (n : ℝ≥0∞) * (309 + 3 * (((2 * (q + 307) : ℕ) : ℝ≥0∞) * ((2 * (q + 307) : ℕ) : ℝ≥0∞) /
          2 ^ 256) + ((q + 307 : ℕ) : ℝ≥0∞) * (3 * (((2 * (q + 307) : ℕ) : ℝ≥0∞) / 2 ^ 256)))
      ≤ (q : ℝ≥0∞) * (1 + (n * n : ℝ≥0∞) * (((2 ^ 128 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 256)) +
          (n : ℝ≥0∞) * (309 + 3 * 1 + 3) := by gcongr
    _ = _ := by push_cast; ring

/-- The per-key terms of the small route, as a fraction over `2^256`. -/
theorem sphincsMulti_rest_le {M N Bn Cq : ℕ} {B c : ℚ} (hN : Sphincs.signatureLimit = N) (hM : M ≤ 2 ^ 128)
    (hB : ENNReal.ofReal (B : ℝ) ≤ (Bn : ℝ≥0∞) / 2 ^ 256)
    (hc : ENNReal.ofReal (c : ℝ) ≤ (Cq : ℝ≥0∞) / 2 ^ 128) :
    smallRestF M B c + 2 * (2 : ℝ≥0∞)⁻¹ ^ 201 + smallFailF M * (2 : ℝ≥0∞)⁻¹ ^ 201 +
        3 * ((M : ℝ≥0∞) / 2 ^ 256) ≤
      ((M * Bn + M ^ 2 * (1 + Cq) + 2 ^ 56 + (M + N) * 2 ^ 56 + 3 * M : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  set M' := M - keygenCost
  have hM' : M' ≤ M := Nat.sub_le _ _
  have hν : PotentialA.ν = (1 : ℝ≥0∞) / 2 ^ 128 := by rw [PotentialA.ν, one_div]
  have i201 : (2 : ℝ≥0∞)⁻¹ ^ 201 = ((2 ^ 55 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [← ENNReal.inv_pow, inv_two_pow_eq 201 (by norm_num), div_eq_mul_inv, Nat.cast_pow,
      Nat.cast_ofNat, show 256 - 201 = 55 from rfl]
  -- the rest
  have r1 : (M' : ℝ≥0∞) * ENNReal.ofReal (B : ℝ) ≤ ((M * Bn : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    calc (M' : ℝ≥0∞) * ENNReal.ofReal (B : ℝ) ≤ (M : ℝ≥0∞) * ((Bn : ℝ≥0∞) / 2 ^ 256) := by
          gcongr
      _ = _ := by rw [Nat.cast_mul, mul_div_assoc]
  have hch : 2 * Nat.choose M' 2 ≤ M ^ 2 := by
    rw [Nat.choose_two_right]
    have := Nat.div_mul_le_self (M' * (M' - 1)) 2
    have h2 : M' * (M' - 1) ≤ M * M := Nat.mul_le_mul hM' (le_trans (Nat.sub_le _ _) hM')
    rw [sq]; omega
  have r2 : PotentialA.ν * ((Nat.choose M' 2 : ℕ) * rateS) ≤ ((M ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    calc PotentialA.ν * ((Nat.choose M' 2 : ℕ) * rateS)
        ≤ 1 / 2 ^ 128 * ((Nat.choose M' 2 : ℕ) * ((2 : ℝ≥0∞) / 2 ^ 128)) := by
          rw [hν]; gcongr; exact sphincsRateS_le
      _ = ((2 * Nat.choose M' 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [show (2 : ℝ≥0∞) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]]
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
            ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
              (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))]
          push_cast; ring
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast hch) _
  have r3 : ((M' : ℝ≥0∞) * PotentialA.ν) * ((M' : ℝ≥0∞) * ENNReal.ofReal (c : ℝ)) ≤
      ((M ^ 2 * Cq : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    calc ((M' : ℝ≥0∞) * PotentialA.ν) * ((M' : ℝ≥0∞) * ENNReal.ofReal (c : ℝ))
        ≤ ((M : ℝ≥0∞) * (1 / 2 ^ 128)) * ((M : ℝ≥0∞) * ((Cq : ℝ≥0∞) / 2 ^ 128)) := by
          rw [hν]; gcongr
      _ = ((M ^ 2 * Cq : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [show (2 : ℝ≥0∞) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]]
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
            ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
              (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))]
          push_cast; ring
  have hrest : smallRestF M B c ≤ ((M * Bn + M ^ 2 * (1 + Cq) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    unfold smallRestF
    calc _ ≤ ((M * Bn : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((M ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
          ((M ^ 2 * Cq : ℕ) : ℝ≥0∞) / 2 ^ 256 := add_le_add (add_le_add r1 r2) r3
      _ = _ := by
          rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ← Nat.cast_add, ← Nat.cast_add]
          congr 2; ring
  -- the failures
  have hMν : (M' : ℝ≥0∞) * PotentialA.ν ≤ 1 := by
    rw [hν, ← mul_div_assoc, mul_one, ENNReal.div_le_iff (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul]
    exact_mod_cast hM'.trans hM
  have hfail : smallFailF M ≤ ((2 * (M + N) : ℕ) : ℝ≥0∞) := by
    unfold smallFailF
    rw [hN]
    calc ((M' : ℝ≥0∞) + (N : ℝ≥0∞)) + ((M' : ℝ≥0∞) * PotentialA.ν) * ((M' : ℝ≥0∞) + (N : ℝ≥0∞))
        ≤ ((M : ℝ≥0∞) + N) + 1 * ((M : ℝ≥0∞) + N) := by gcongr
      _ = _ := by push_cast; ring
  calc smallRestF M B c + 2 * (2 : ℝ≥0∞)⁻¹ ^ 201 + smallFailF M * (2 : ℝ≥0∞)⁻¹ ^ 201 +
        3 * ((M : ℝ≥0∞) / 2 ^ 256)
      ≤ ((M * Bn + M ^ 2 * (1 + Cq) : ℕ) : ℝ≥0∞) / 2 ^ 256 +
          2 * (((2 ^ 55 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
          ((2 * (M + N) : ℕ) : ℝ≥0∞) * (((2 ^ 55 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
          3 * ((M : ℝ≥0∞) / 2 ^ 256) := by
        rw [i201]; gcongr
    _ = _ := by
        generalize ((2 : ℝ≥0∞) ^ 256) = T
        simp only [div_eq_mul_inv]
        push_cast
        ring

/-- **`multiSmall` as a fraction over `2^256`**, at a budget of the small route. -/
theorem multiSmall_le_num {n q X F Xa N Bn Cq : ℕ} {ρ : ℝ} {B c : ℚ}
    (hX : ENNReal.ofReal (ρ / 2 ^ 128) ≤ (X : ℝ≥0∞) / 2 ^ 256) (hF : 2 ≤ F)
    (hMX : 2 * (q + 307) * X * F ≤ 2 ^ 256) (hXa : F * X ≤ (F - 1) * Xa)
    (hXa4 : Xa * (2 ^ 128 + 2) ≤ 4 * 2 ^ 256) (hM : 2 * (q + 307) ≤ 2 ^ 128)
    (hN : Sphincs.signatureLimit = N) (hB : ENNReal.ofReal (B : ℝ) ≤ (Bn : ℝ≥0∞) / 2 ^ 256)
    (hc : ENNReal.ofReal (c : ℝ) ≤ (Cq : ℝ≥0∞) / 2 ^ 128) :
    multiSmall n q ρ B c ≤
      ((Xa * q + 4 * n ^ 2 * q + 315 * Xa * n +
        n * (2 * (q + 307) * Bn + (2 * (q + 307)) ^ 2 * (1 + Cq) + 2 ^ 56 +
          (2 * (q + 307) + N) * 2 ^ 56 + 3 * (2 * (q + 307))) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have hmain := sphincsMulti_main_le (M := 2 * (q + 307)) hX hF hMX hXa
  have hsum := sphincsMulti_sum_le (n := n) hM
  have hrest := sphincsMulti_rest_le (M := 2 * (q + 307)) hN hM hB hc
  unfold multiSmall
  have hpc : (Xa : ℝ≥0∞) / 2 ^ 256 * (((2 ^ 128 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤
      (4 : ℝ≥0∞) / 2 ^ 256 := by
    have e4 : (4 : ℝ≥0∞) / 2 ^ 256 = ((4 * 2 ^ 256 : ℕ) : ℝ≥0∞) / 2 ^ (256 + 256) := by
      rw [pow_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat,
        ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ two_ne_zero)
          (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
    rw [natDiv_mul_natDiv, e4]
    exact ENNReal.div_le_div_right (by exact_mod_cast hXa4) _
  calc _ ≤ (Xa : ℝ≥0∞) / 2 ^ 256 * ((q : ℝ≥0∞) + (q * n ^ 2 : ℕ) *
          (((2 ^ 128 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) + ((315 * n : ℕ) : ℝ≥0∞)) +
        (n : ℝ≥0∞) * (((2 * (q + 307) * Bn + (2 * (q + 307)) ^ 2 * (1 + Cq) + 2 ^ 56 +
          (2 * (q + 307) + N) * 2 ^ 56 + 3 * (2 * (q + 307)) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
        gcongr
    _ = (Xa : ℝ≥0∞) / 2 ^ 256 * q + ((q * n ^ 2 : ℕ) : ℝ≥0∞) *
          ((Xa : ℝ≥0∞) / 2 ^ 256 * (((2 ^ 128 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 256)) +
        (Xa : ℝ≥0∞) / 2 ^ 256 * ((315 * n : ℕ) : ℝ≥0∞) +
        (n : ℝ≥0∞) * (((2 * (q + 307) * Bn + (2 * (q + 307)) ^ 2 * (1 + Cq) + 2 ^ 56 +
          (2 * (q + 307) + N) * 2 ^ 56 + 3 * (2 * (q + 307)) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by ring
    _ ≤ (Xa : ℝ≥0∞) / 2 ^ 256 * q + ((q * n ^ 2 : ℕ) : ℝ≥0∞) * ((4 : ℝ≥0∞) / 2 ^ 256) +
        (Xa : ℝ≥0∞) / 2 ^ 256 * ((315 * n : ℕ) : ℝ≥0∞) +
        (n : ℝ≥0∞) * (((2 * (q + 307) * Bn + (2 * (q + 307)) ^ 2 * (1 + Cq) + 2 ^ 56 +
          (2 * (q + 307) + N) * 2 ^ 56 + 3 * (2 * (q + 307)) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
        gcongr
    _ = _ := by
        generalize ((2 : ℝ≥0∞) ^ 256) = T
        simp only [div_eq_mul_inv]
        push_cast
        ring

/-- **`multiBound` at `Q + 686`, linear plus quadratic.** With `n ≥ 1` keys whose key generations
(`K` hash calls each) the count `Q` pays for, leanSPHINCS's per-key bound is at most
`(Q (La + Lb n + 4 n²) + D n Q²)/2^256`, given the numeric facts of a parameter set. -/
theorem multiBound_le_sharp {n Q qh kc X F Xa N Bn Cq K La Lb D : ℕ} {ρ : ℝ} {B c : ℚ}
    (hkc : keygenCost = kc)
    (hX : ENNReal.ofReal (ρ / 2 ^ 128) ≤ (X : ℝ≥0∞) / 2 ^ 256) (hF : 2 ≤ F)
    (hXF : (qh + kc) * X * F ≤ 2 ^ 256) (hXa : F * X ≤ (F - 1) * Xa)
    (hXa4 : Xa * (2 ^ 128 + 2) ≤ 4 * 2 ^ 256) (hqh : qh + kc ≤ 2 ^ 128)
    (hN : Sphincs.signatureLimit = N) (hB : ENNReal.ofReal (B : ℝ) ≤ (Bn : ℝ≥0∞) / 2 ^ 256)
    (hc : ENNReal.ofReal (c : ℝ) ≤ (Cq : ℝ≥0∞) / 2 ^ 128)
    (hLa : 1001 * Xa + (1986 * Bn + 1986 ^ 2 * (1 + Cq) + 2 ^ 56 + (1986 + N) * 2 ^ 56 + 5958) ≤
      (La - Xa) * K) (hLaX : Xa ≤ La)
    (hLb : 2 * Bn + 7944 * (1 + Cq) + 2 ^ 57 + 6 + 2744 ≤ Lb) (hD : 4 * (1 + Cq) ≤ D)
    (hDT : 2 ^ 131 ≤ D * (qh + kc - 1985)) (hK : 2 ^ 10 ≤ K)
    (hn : 1 ≤ n) (hQ : n * K ≤ Q) :
    multiBound n qh ρ B c (Q + 686) ≤
      ((Q * (La + Lb * n + 4 * n ^ 2) + D * n * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have hQK : K ≤ Q := le_trans (Nat.le_mul_of_pos_left K hn) hQ
  unfold multiBound
  rw [hkc]
  split_ifs with hsm
  · have hM1 : 2 * (Q + 686 + 307) ≤ qh + kc := Nat.sub_le_iff_le_add.mp hsm
    have hMX : 2 * (Q + 686 + 307) * X * F ≤ 2 ^ 256 :=
      le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hM1)) hXF
    have hM : 2 * (Q + 686 + 307) ≤ 2 ^ 128 := le_trans hM1 hqh
    refine (min_le_left _ _).trans ((multiSmall_le_num (n := n) (q := Q + 686) hX hF hMX hXa hXa4
      hM hN hB hc).trans (ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _))
    -- the numerators
    set C0 := 1986 * Bn + 1986 ^ 2 * (1 + Cq) + 2 ^ 56 + (1986 + N) * 2 ^ 56 + 5958
    set Lb0 := 2 * Bn + 7944 * (1 + Cq) + 2 ^ 57 + 6
    set Lc := La - Xa
    have hc1 : 1001 * (Xa * n) + C0 * n ≤ Lc * Q :=
      calc _ = (1001 * Xa + C0) * n := by ring
        _ ≤ Lc * K * n := Nat.mul_le_mul_right _ hLa
        _ = Lc * (n * K) := by ring
        _ ≤ Lc * Q := Nat.mul_le_mul_left _ hQ
    have hc2 : 2744 * (n * n) ≤ 2744 * (n * Q) := by
      have : n ≤ Q := le_trans (Nat.le_mul_of_pos_right n (by omega)) hQ
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
    have hc3 : Lb0 * (n * Q) + 2744 * (n * Q) ≤ Lb * (n * Q) := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hLb
    have hc4 : 4 * (1 + Cq) * (n * Q ^ 2) ≤ D * (n * Q ^ 2) := Nat.mul_le_mul_right _ hD
    have hc5 : 686 * Xa + 315 * (Xa * n) ≤ 1001 * (Xa * n) := by
      have h := Nat.mul_le_mul_left Xa hn
      rw [Nat.mul_one] at h
      omega
    have hLa' : La = Xa + Lc := by omega
    have e1 : Xa * (Q + 686) + 4 * n ^ 2 * (Q + 686) + 315 * Xa * n +
        n * (2 * (Q + 686 + 307) * Bn + (2 * (Q + 686 + 307)) ^ 2 * (1 + Cq) + 2 ^ 56 +
          (2 * (Q + 686 + 307) + N) * 2 ^ 56 + 3 * (2 * (Q + 686 + 307))) =
        Xa * Q + 4 * (n ^ 2 * Q) + Lb0 * (n * Q) + 4 * (1 + Cq) * (n * Q ^ 2) +
          (686 * Xa + 2744 * (n * n) + 315 * (Xa * n) + C0 * n) := by
      simp only [C0, Lb0]; ring
    have e2 : Q * (La + Lb * n + 4 * n ^ 2) + D * n * Q ^ 2 =
        Xa * Q + Lc * Q + Lb * (n * Q) + 4 * (n ^ 2 * Q) + D * (n * Q ^ 2) := by
      rw [hLa']; ring
    rw [e1, e2]
    clear_value C0 Lb0 Lc
    clear e1 e2 hXF hXa4 hqh hDT hMX hM hM1 hsm hX hB hc hLa hLb
    omega
  · -- beyond the small route: `n q/2^127 ≤ D n q²/2^256`
    have hlt : qh + kc < 2 * (Q + 686 + 307) := Nat.lt_sub_iff_add_lt.mp (Nat.lt_of_not_le hsm)
    have hlarge : qh + kc - 1985 ≤ 2 * Q := by
      clear hXF hXa4 hqh hLa hLb hDT hX hB hc hD hsm
      omega
    have hDQ : 2 ^ 130 ≤ D * Q := by
      have h := Nat.mul_le_mul_left D hlarge
      have h2 : 2 * 2 ^ 130 ≤ 2 * (D * Q) :=
        calc 2 * 2 ^ 130 = 2 ^ 131 := by norm_num
          _ ≤ D * (qh + kc - 1985) := hDT
          _ ≤ D * (2 * Q) := h
          _ = 2 * (D * Q) := by ring
      exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
    rw [sphincsMultiClosed_eq_num]
    refine ENNReal.div_le_div_right ?_ _
    have h686 : 686 ≤ Q := le_trans (le_trans (by norm_num : 686 ≤ 2 ^ 10) hK) hQK
    have h1 : 2 ^ 129 * (n * (Q + 686)) ≤ 2 ^ 130 * (n * Q) := by
      have : n * (Q + 686) ≤ 2 * (n * Q) := by
        have := Nat.mul_le_mul_left n h686
        linarith
      calc 2 ^ 129 * (n * (Q + 686)) ≤ 2 ^ 129 * (2 * (n * Q)) := Nat.mul_le_mul_left _ this
        _ = 2 ^ 130 * (n * Q) := by ring
    have h2 : 2 ^ 130 * (n * Q) ≤ D * Q * (n * Q) := Nat.mul_le_mul_right _ hDQ
    have e : D * Q * (n * Q) = D * n * Q ^ 2 := by ring
    have h3 : D * n * Q ^ 2 ≤ Q * (La + Lb * n + 4 * n ^ 2) + D * n * Q ^ 2 := Nat.le_add_left _ _
    have h4 : 2 ^ 129 * (n * (Q + 686)) ≤ Q * (La + Lb * n + 4 * n ^ 2) + D * n * Q ^ 2 :=
      (h1.trans h2).trans (e ▸ h3)
    exact_mod_cast h4

end Generic

/-! ## The sharp parameter sets -/

/-- **A leanSPHINCS parameter set with its sharp multi-user bound**: the bound `sharpBound n`
(`Multi.multiBound` at the set's certificates), and its linear-plus-quadratic form at `Q + 686`
for `n ≥ 1` keys whose key generations `Q` counts. -/
class SphincsSetSharp (P : Sphincs.Params) extends SphincsSet P where
  sharpBound : ℕ → ℕ → ℝ≥0∞
  sharp : ∀ n, @Sphincs.Security.Multi.HasMultiUserBound P n (sharpBound n)
  /-- The linear numerator free of `n` (over `2^256`). -/
  linA : ℕ
  /-- The linear numerator per key. -/
  linB : ℕ
  /-- The quadratic coefficient per key (over `2^256`). -/
  quadD : ℕ
  sharp_le : ∀ n Q, 1 ≤ n → n * keygenCost ≤ Q →
    sharpBound n (Q + 686) ≤
      ((Q * (linA + linB * n + 4 * n ^ 2) + quadD * n * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- **The sharp linear rate** `2^-λ₁`: T1 and leanXMSS as in the headline, and leanSPHINCS's
sharp per-key bound. -/
noncomputable def noForgeryRateSharp [P : Sphincs.Params] [S : SphincsSetSharp P] (nx ns : ℕ) :
    ℝ≥0∞ :=
  ((noForgeryRateNum nx 0 + S.linA + S.linB * ns + 4 * ns ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

/-! ## The headline, sharp -/

/-- T5 with the cubic T3 and leanSPHINCS's bound `εs`, with no term for a scheme without keys. -/
theorem prEvent_breaks_le_split' [P : Sphincs.Params] {nx ns : ℕ}
    {εs : ℕ → ℝ≥0∞} (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS)
    (hq : gameQueries nx ns qH sX sS budget + 384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      aggBadError2 (gameQueries nx ns qH sX sS budget) +
        (if nx = 0 then 0 else xmssMultiError nx (gameQueries nx ns qH sX sS budget + 384)) +
        (if ns = 0 then 0 else εs (gameQueries nx ns qH sX sS budget + 686)) := by
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
  · split_ifs with hns
    · subst hns
      exact le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun z h ↦ by
        obtain ⟨-, ⟨j, -⟩, -⟩ := h; exact j.elim0)
    · refine (prEvent_forgedS_le_bound2 hG hsph keygenFromSeed_isTotalQueryBound
        sphincsKeygenFromSeed_isTotalQueryBound sign_isTotalQueryBound
        sphincsSign_isTotalQueryBound sphincsVerify_isTotalQueryBound fuel budget A hA.hash
        hA.xmss hA.sphincs).trans (le_of_eq ?_)
      have hm : max 1 (Q + sphincsVerifyBound) = Q + 686 :=
        max_eq_right (by unfold sphincsVerifyBound; omega)
      simp only [show nx * xmssKeygenBound + ns * sphincsKeygenBound +
        (qH + sX * xmssSignBound + sS * sphincsSignBound) + budget + sphincsVerifyBound =
          Q + sphincsVerifyBound from rfl, hm]

/-- The game's hash evaluations pay for the leanSPHINCS key generations. -/
theorem sphincsKeygens_le_gameQueries [P : Sphincs.Params] [S : SphincsSet P]
    (nx ns qH sX sS budget : ℕ) : ns * S.keygenCost ≤ gameQueries nx ns qH sX sS budget := by
  rw [← S.keygen_eq]
  unfold gameQueries
  exact le_trans (Nat.le_add_left _ (nx * xmssKeygenBound))
    (Nat.le_add_right_of_le (Nat.le_add_right _ _))

/-- **No forgery with leanSPHINCS's sharp bound, at any fuel and budget.** -/
theorem aggregate_no_forgery_linear_sharp [P : Sphincs.Params] [S : SphincsSetSharp P] {nx ns : ℕ}
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      (gameQueries nx ns qH sX sS budget : ℝ≥0∞) * noForgeryRateSharp nx ns +
        (((30 + S.quadD * ns) * gameQueries nx ns qH sX sS budget ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  set Q := gameQueries nx ns qH sX sS budget
  have hK := keygens_le_gameQueries (S := S.toSphincsSet) nx ns qH sX sS budget
  have hKs : ns * S.keygenCost ≤ Q := sphincsKeygens_le_gameQueries nx ns qH sX sS budget
  by_cases hq : Q + 384 < 2 ^ 126
  · have hK0 : nx * 2 ^ 23 + 0 * 2 ^ 15 ≤ Q := by
      rw [Nat.zero_mul, Nat.add_zero]; exact le_trans (Nat.le_add_right _ _) hK
    have hcore := chainCoreNum_le (nx := nx) (ns := 0) (Q := Q) hK0
    have hS : (if ns = 0 then 0 else S.sharpBound ns (Q + 686)) ≤
        ((Q * (S.linA + S.linB * ns + 4 * ns ^ 2) + S.quadD * ns * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
      split_ifs with hns
      · exact zero_le
      · exact S.sharp_le ns Q (Nat.one_le_iff_ne_zero.mpr hns) hKs
    calc Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2]
        ≤ aggBadError2 Q + (if nx = 0 then 0 else xmssMultiError nx (Q + 384)) +
            (if ns = 0 then 0 else S.sharpBound ns (Q + 686)) :=
          prEvent_breaks_le_split' (S.sharp ns) fuel budget A hA hq
      _ = ((chainCoreNum Q : ℝ≥0∞) / 2 ^ 256 +
            (if nx = 0 then 0 else xmssMultiError nx (Q + 384))) +
            (if ns = 0 then 0 else S.sharpBound ns (Q + 686)) + predError2 Q := by
          rw [aggBadError2_eq_core]; ring
      _ ≤ ((Q * noForgeryRateNum nx 0 + 29 * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
            ((Q * (S.linA + S.linB * ns + 4 * ns ^ 2) + S.quadD * ns * Q ^ 2 : ℕ) : ℝ≥0∞) /
              2 ^ 256 + ((Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          have hQ128 : Q ≤ 2 ^ 128 :=
            le_trans (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_add_right Q 384) hq)) (by norm_num)
          refine add_le_add (add_le_add ?_ hS) (predError2_le_sq hQ128)
          split_ifs at hcore ⊢ with hnx
          · rw [add_zero]
            refine ENNReal.div_le_div_right ?_ _
            exact_mod_cast (by simpa using hcore)
          · rw [xmssMultiError_eq_num, ENNReal.div_add_div_same, ← Nat.cast_add]
            refine ENNReal.div_le_div_right ?_ _
            exact_mod_cast (by simpa using hcore)
      _ = (Q : ℝ≥0∞) * noForgeryRateSharp nx ns +
            (((30 + S.quadD * ns) * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [noForgeryRateSharp, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
            ← Nat.cast_add, ← Nat.cast_add, ← mul_div_assoc, ← Nat.cast_mul,
            ENNReal.div_add_div_same, ← Nat.cast_add]
          congr 2; ring
  · refine (prEvent_le_one _).trans ((one_le_quad_of_large (c := 30 + S.quadD * ns)
      (by omega) hq).trans le_add_self)

/-- **No forgery with leanSPHINCS's sharp bound (the sharp headline).** As
`aggregate_no_forgery_final`, with `Pr[Breaks] ≤ q · noForgeryRateSharp n_x n_s +
(30 + D n_s) q²/2^256`, `D = SphincsSetSharp.quadD`. -/
theorem aggregate_no_forgery_final_sharp [P : Sphincs.Params] [S : SphincsSetSharp P] {nx ns : ℕ}
    (N : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      (totalQueries nx ns qH sX sS N : ℝ≥0∞) * noForgeryRateSharp nx ns +
        (((30 + S.quadD * ns) * totalQueries nx ns qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  aggregate_no_forgery_linear_sharp N (viCost N) A hA

section Full

attribute [local instance] Sphincs.Lifetimes.full

theorem sharpB_b26 : Sphincs.Security.H0.small_b26.B =
    4593355021251507 / 1569275433846670190958947355801916604025588861116008628224 := by
  decide +kernel

theorem sharpEn_b26 : Sphincs.Security.H0.near_b26.En =
    314681146978208084124729273593 / 3533694129556768659166595001485837031654967793751237916243212402585239552 := by
  decide +kernel

/-- leanSPHINCS's sharp multi-user bound at subtree height 26 (`full_multiUserKey`). -/
noncomputable def sharpBoundFull (n : ℕ) : ℕ → ℝ≥0∞ :=
  Sphincs.Security.Multi.multiBound n 250752950924986904089568310569467904
    (Sphincs.Security.H0.rho_b26 : ℝ) Sphincs.Security.H0.small_b26.B
    ((2 - Sphincs.Security.H0.rho_b26 + ((250752950924986904089568310569467904 : ℕ) : ℚ) / 2 ^ 128 +
      ((1383000000 : ℕ) : ℚ) * 123 / (2 ^ 26 * 2 ^ 15)) *
      ((2 ^ 26 * Sphincs.Security.H0.near_b26.En : ℚ) / 2))

/-- Subtree height 26, sharp. -/
noncomputable instance sphincsSetSharpFull : SphincsSetSharp Sphincs.Lifetimes.full where
  toSphincsSet := sphincsSetFull
  sharpBound := sharpBoundFull
  sharp n := (Sphincs.Lifetimes.requestedMultiUserKey n).1
  linA := 596040671069167063820405666386271274653
  linB := 677859556133721986326185045152818246
  quadD := 10857
  sharp_le n Q hn hQ := by
    refine multiBound_le_sharp (kc := 15166603264) (F := 512) (N := 1383000000) (Cq := 336)
      (K := 15166603265)
      (X := 594876489827177958560772659465567600640)
      (Xa := 596040631685939559262457146079003153675)
      (Bn := 338929778066860993091034928537141248)
      (by decide) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl ?_ ?_ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn hQ
    · rw [show (Sphincs.Security.H0.rho_b26 : ℝ) / 2 ^ 128 =
          ((Sphincs.Security.H0.rho_b26 / 2 ^ 128 : ℚ) : ℝ) by rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]]
      exact ofReal_rat_le_div (by unfold Sphincs.Security.H0.rho_b26; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpB_b26]; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpEn_b26]; unfold Sphincs.Security.H0.rho_b26; norm_num)

end Full

section Pruned20

attribute [local instance] Sphincs.Lifetimes.pruned20

theorem sharpB_b20 : Sphincs.Security.H0.small_b20.B =
    8270464498964157 / 1569275433846670190958947355801916604025588861116008628224 := by
  decide +kernel

theorem sharpEn_b20 : Sphincs.Security.H0.near_b20.En =
    3279495189070586115593799221 / 1725436586697640946858688965569256363112777243042596638790631055949824 := by
  decide +kernel

/-- leanSPHINCS's sharp multi-user bound at subtree height 20 (`pruned20_multiUserKey`). -/
noncomputable def sharpBoundPruned20 (n : ℕ) : ℕ → ℝ≥0∞ :=
  Sphincs.Security.Multi.multiBound n 558871528355207643822193711415033856
    (Sphincs.Security.H0.rho_b20 : ℝ) Sphincs.Security.H0.small_b20.B
    ((2 - Sphincs.Security.H0.rho_b20 + ((558871528355207643822193711415033856 : ℕ) : ℚ) / 2 ^ 128 +
      ((26030000 : ℕ) : ℚ) * 123 / (2 ^ 20 * 2 ^ 15)) *
      ((2 ^ 20 * Sphincs.Security.H0.near_b20.En : ℚ) / 2))

/-- Subtree height 20, sharp. -/
noncomputable instance sphincsSetSharpPruned20 : SphincsSetSharp Sphincs.Lifetimes.pruned20 where
  toSphincsSet := sphincsSetPruned20
  sharpBound := sharpBoundPruned20
  sharp n := (Sphincs.Lifetimes.requestedMultiUserKey n).2.1
  linA := 638416827155798388185149920495212771898
  linB := 1220505135864738393980132059479899950
  quadD := 4871
  sharp_le n Q hn hQ := by
    refine multiBound_le_sharp (kc := 236978188) (F := 256) (N := 26030000) (Cq := 77)
      (K := 236978189)
      (X := 635920320191951578189024685112317444096)
      (Xa := 638414125369174917711334585838248100740)
      (Bn := 610252567932369196918008435701710848)
      (by decide) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl ?_ ?_ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn hQ
    · rw [show (Sphincs.Security.H0.rho_b20 : ℝ) / 2 ^ 128 =
          ((Sphincs.Security.H0.rho_b20 / 2 ^ 128 : ℚ) : ℝ) by rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]]
      exact ofReal_rat_le_div (by unfold Sphincs.Security.H0.rho_b20; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpB_b20]; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpEn_b20]; unfold Sphincs.Security.H0.rho_b20; norm_num)

end Pruned20

section Pruned14

attribute [local instance] Sphincs.Lifetimes.pruned14

theorem sharpB_b14 : Sphincs.Security.H0.small_b14.B =
    4108944699504613 / 392318858461667547739736838950479151006397215279002157056 := by
  decide +kernel

theorem sharpEn_b14 : Sphincs.Security.H0.near_b14.En =
    3552773432689369213538207 / 105312291668557186697918027683670432318895095400549111254310977536 := by
  decide +kernel

/-- leanSPHINCS's sharp multi-user bound at subtree height 14 (`pruned14_multiUserKey`). -/
noncomputable def sharpBoundPruned14 (n : ℕ) : ℕ → ℝ≥0∞ :=
  Sphincs.Security.Multi.multiBound n 1179940068462340716375613534384422912
    (Sphincs.Security.H0.rho_b14 : ℝ) Sphincs.Security.H0.small_b14.B
    ((2 - Sphincs.Security.H0.rho_b14 + ((1179940068462340716375613534384422912 : ℕ) : ℚ) / 2 ^ 128 +
      ((480900 : ℕ) : ℚ) * 123 / (2 ^ 14 * 2 ^ 15)) *
      ((2 ^ 14 * Sphincs.Security.H0.near_b14.En : ℚ) / 2))

/-- Subtree height 14, sharp. -/
noncomputable instance sphincsSetSharpPruned14 : SphincsSetSharp Sphincs.Lifetimes.pruned14 where
  toSphincsSet := sphincsSetPruned14
  sharpBound := sharpBoundPruned14
  sharp n := (Sphincs.Lifetimes.requestedMultiUserKey n).2.2.1
  linA := 663210424649718332295806487435111576337
  linB := 2425492841113183816000015397791349070
  quadD := 2308
  sharp_le n Q hn hQ := by
    refine multiBound_le_sharp (kc := 3702808) (F := 128) (N := 480900) (Cq := 17)
      (K := 3702809)
      (X := 657850607588232989281832953105419862016)
      (Xa := 663030533632234823843107228326722380615)
      (Bn := 1212746420556591907927950104857673728)
      (by decide) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl ?_ ?_ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn hQ
    · rw [show (Sphincs.Security.H0.rho_b14 : ℝ) / 2 ^ 128 =
          ((Sphincs.Security.H0.rho_b14 / 2 ^ 128 : ℚ) : ℝ) by rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]]
      exact ofReal_rat_le_div (by unfold Sphincs.Security.H0.rho_b14; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpB_b14]; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpEn_b14]; unfold Sphincs.Security.H0.rho_b14; norm_num)

end Pruned14

section Pruned13

attribute [local instance] Sphincs.Lifetimes.pruned13

theorem sharpB_b13 : Sphincs.Security.H0.small_b13.B =
    36128254553371509 / 3138550867693340381917894711603833208051177722232017256448 := by
  decide +kernel

theorem sharpEn_b13 : Sphincs.Security.H0.near_b13.En =
    11392308424728151518941903 / 210624583337114373395836055367340864637790190801098222508621955072 := by
  decide +kernel

/-- leanSPHINCS's sharp multi-user bound at subtree height 13 (`pruned13_multiUserKey`). -/
noncomputable def sharpBoundPruned13 (n : ℕ) : ℕ → ℝ≥0∞ :=
  Sphincs.Security.Multi.multiBound n 1314909569352122321482228451418046464
    (Sphincs.Security.H0.rho_b13 : ℝ) Sphincs.Security.H0.small_b13.B
    ((2 - Sphincs.Security.H0.rho_b13 + ((1314909569352122321482228451418046464 : ℕ) : ℚ) / 2 ^ 128 +
      ((247000 : ℕ) : ℚ) * 123 / (2 ^ 13 * 2 ^ 15)) *
      ((2 ^ 13 * Sphincs.Security.H0.near_b13.En : ℚ) / 2))

/-- Subtree height 13, sharp. -/
noncomputable instance sphincsSetSharpPruned13 : SphincsSetSharp Sphincs.Lifetimes.pruned13 where
  toSphincsSet := sphincsSetPruned13
  sharpBound := sharpBoundPruned13
  sharp n := (Sphincs.Lifetimes.requestedMultiUserKey n).2.2.2.1
  linA := 665599770187604638693452452572106817731
  linB := 2665794662303504029001796265913211958
  quadD := 2071
  sharp_le n Q hn hQ := by
    refine multiBound_le_sharp (kc := 1851418) (F := 128) (N := 247000) (Cq := 14)
      (K := 1851419)
      (X := 660041491126016368531521667641620037632)
      (Xa := 665238668221496812378226562662420195409)
      (Bn := 1332897331151752014428840538918617088)
      (by decide) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl ?_ ?_ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn hQ
    · rw [show (Sphincs.Security.H0.rho_b13 : ℝ) / 2 ^ 128 =
          ((Sphincs.Security.H0.rho_b13 / 2 ^ 128 : ℚ) : ℝ) by rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]]
      exact ofReal_rat_le_div (by unfold Sphincs.Security.H0.rho_b13; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpB_b13]; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpEn_b13]; unfold Sphincs.Security.H0.rho_b13; norm_num)

end Pruned13

section Pruned12

attribute [local instance] Sphincs.Lifetimes.pruned12

theorem sharpB_b12 : Sphincs.Security.H0.small_b12.B =
    40025809671818887 / 3138550867693340381917894711603833208051177722232017256448 := by
  decide +kernel

theorem sharpEn_b12 : Sphincs.Security.H0.near_b12.En =
    4602660197465026464511015 / 52656145834278593348959013841835216159447547700274555627155488768 := by
  decide +kernel

/-- leanSPHINCS's sharp multi-user bound at subtree height 12 (`pruned12_multiUserKey`). -/
noncomputable def sharpBoundPruned12 (n : ℕ) : ℕ → ℝ≥0∞ :=
  Sphincs.Security.Multi.multiBound n 1449533407878593313898110627080044544
    (Sphincs.Security.H0.rho_b12 : ℝ) Sphincs.Security.H0.small_b12.B
    ((2 - Sphincs.Security.H0.rho_b12 + ((1449533407878593313898110627080044544 : ℕ) : ℚ) / 2 ^ 128 +
      ((126900 : ℕ) : ℚ) * 123 / (2 ^ 12 * 2 ^ 15)) *
      ((2 ^ 12 * Sphincs.Security.H0.near_b12.En : ℚ) / 2))

/-- Subtree height 12, sharp. -/
noncomputable instance sphincsSetSharpPruned12 : SphincsSetSharp Sphincs.Lifetimes.pruned12 where
  toSphincsSet := sphincsSetPruned12
  sharpBound := sharpBoundPruned12
  sharp n := (Sphincs.Lifetimes.requestedMultiUserKey n).2.2.2.2.1
  linA := 673078321939232683130339554499435801749
  linB := 2953383469436206027468332275796639518
  quadD := 1879
  sharp_le n Q hn hQ := by
    refine multiBound_le_sharp (kc := 925724) (F := 64) (N := 126900) (Cq := 11)
      (K := 925725)
      (X := 661842694446748799716169263535366340608)
      (Xa := 672348134041141637806902108988308663475)
      (Bn := 1476691734718103013662108543860342784)
      (by decide) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl ?_ ?_ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn hQ
    · rw [show (Sphincs.Security.H0.rho_b12 : ℝ) / 2 ^ 128 =
          ((Sphincs.Security.H0.rho_b12 / 2 ^ 128 : ℚ) : ℝ) by rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]]
      exact ofReal_rat_le_div (by unfold Sphincs.Security.H0.rho_b12; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpB_b12]; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpEn_b12]; unfold Sphincs.Security.H0.rho_b12; norm_num)

end Pruned12

section Pruned10

attribute [local instance] Sphincs.Lifetimes.pruned10

theorem sharpB_b10 : Sphincs.Security.H0.small_b10.B =
    48210856699268753 / 3138550867693340381917894711603833208051177722232017256448 := by
  decide +kernel

theorem sharpEn_b10 : Sphincs.Security.H0.near_b10.En =
    94457045421343124297597 / 411376139330301510538742295639337626245683966408394965837152256 := by
  decide +kernel

/-- leanSPHINCS's sharp multi-user bound at subtree height 10 (`pruned10_multiUserKey`). -/
noncomputable def sharpBoundPruned10 (n : ℕ) : ℕ → ℝ≥0∞ :=
  Sphincs.Security.Multi.multiBound n 1742566343746827758207774509045383168
    (Sphincs.Security.H0.rho_b10 : ℝ) Sphincs.Security.H0.small_b10.B
    ((2 - Sphincs.Security.H0.rho_b10 + ((1742566343746827758207774509045383168 : ℕ) : ℚ) / 2 ^ 128 +
      ((33490 : ℕ) : ℚ) * 123 / (2 ^ 10 * 2 ^ 15)) *
      ((2 ^ 10 * Sphincs.Security.H0.near_b10.En : ℚ) / 2))

/-- Subtree height 10, sharp. -/
noncomputable instance sphincsSetSharpPruned10 : SphincsSetSharp Sphincs.Lifetimes.pruned10 where
  toSphincsSet := sphincsSetPruned10
  sharpBound := sharpBoundPruned10
  sharp n := (Sphincs.Lifetimes.requestedMultiUserKey n).2.2.2.2.2.1
  linA := 678334904649308170983344953256249483381
  linB := 3557333340422785216610361342913741566
  quadD := 1563
  sharp_le n Q hn hQ := by
    refine multiBound_le_sharp (kc := 231456) (F := 64) (N := 33490) (Cq := 7)
      (K := 231457)
      (X := 664845589336615144916694805150055792640)
      (Xa := 675398693929259829756642341739739217920)
      (Bn := 1778666670211392608233123077418909696)
      (by decide) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl ?_ ?_ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn hQ
    · rw [show (Sphincs.Security.H0.rho_b10 : ℝ) / 2 ^ 128 =
          ((Sphincs.Security.H0.rho_b10 / 2 ^ 128 : ℚ) : ℝ) by rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]]
      exact ofReal_rat_le_div (by unfold Sphincs.Security.H0.rho_b10; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpB_b10]; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpEn_b10]; unfold Sphincs.Security.H0.rho_b10; norm_num)

end Pruned10

section Pruned8

attribute [local instance] Sphincs.Lifetimes.pruned8

theorem sharpB_b8 : Sphincs.Security.H0.small_b8.B =
    13591040036421191 / 784637716923335095479473677900958302012794430558004314112 := by
  decide +kernel

theorem sharpEn_b8 : Sphincs.Security.H0.near_b8.En =
    30852539122443071326743 / 51422017416287688817342786954917203280710495801049370729644032 := by
  decide +kernel

/-- leanSPHINCS's sharp multi-user bound at subtree height 8 (`pruned8_multiUserKey`). -/
noncomputable def sharpBoundPruned8 (n : ℕ) : ℕ → ℝ≥0∞ :=
  Sphincs.Security.Multi.multiBound n 2027867772287336761555281578532274176
    (Sphincs.Security.H0.rho_b8 : ℝ) Sphincs.Security.H0.small_b8.B
    ((2 - Sphincs.Security.H0.rho_b8 + ((2027867772287336761555281578532274176 : ℕ) : ℚ) / 2 ^ 128 +
      ((8830 : ℕ) : ℚ) * 123 / (2 ^ 8 * 2 ^ 15)) *
      ((2 ^ 8 * Sphincs.Security.H0.near_b8.En : ℚ) / 2))

/-- Subtree height 8, sharp. -/
noncomputable instance sphincsSetSharpPruned8 : SphincsSetSharp Sphincs.Lifetimes.pruned8 where
  toSphincsSet := sphincsSetPruned8
  sharpBound := sharpBoundPruned8
  sharp n := (Sphincs.Lifetimes.requestedMultiUserKey n).2.2.2.2.2.2
  linA := 689339656776182513247579718366233371071
  linB := 4011366995958429658253143954967020782
  quadD := 1343
  sharp_le n Q hn hQ := by
    refine multiBound_le_sharp (kc := 57892) (F := 64) (N := 8830) (Cq := 5)
      (K := 57893)
      (X := 666968759584471278293370188425766895616)
      (Xa := 677555565292161298583741143797604465388)
      (Bn := 2005683497979214829054514383445557248)
      (by decide) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl ?_ ?_ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn hQ
    · rw [show (Sphincs.Security.H0.rho_b8 : ℝ) / 2 ^ 128 =
          ((Sphincs.Security.H0.rho_b8 / 2 ^ 128 : ℚ) : ℝ) by rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]]
      exact ofReal_rat_le_div (by unfold Sphincs.Security.H0.rho_b8; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpB_b8]; norm_num)
    · exact ofReal_rat_le_div (by rw [sharpEn_b8]; unfold Sphincs.Security.H0.rho_b8; norm_num)

end Pruned8

/-! ## The deployed sets at `2^20 + 2^20` keys -/

/-- A sharp rate's numerator below `2^(256 − k)` is `2^-k`. -/
theorem noForgeryRateSharp_le_of [P : Sphincs.Params] [S : SphincsSetSharp P] {nx ns k : ℕ}
    (hk : k ≤ 256)
    (h : noForgeryRateNum nx 0 + S.linA + S.linB * ns + 4 * ns ^ 2 ≤ 2 ^ (256 - k)) :
    noForgeryRateSharp nx ns ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
  rw [noForgeryRateSharp, ← ENNReal.inv_pow, inv_two_pow_eq k hk, div_eq_mul_inv]
  gcongr
  exact_mod_cast h

section FullDeployed

attribute [local instance] Sphincs.Lifetimes.full

/-- **`full`, `2^20 + 2^20` keys: `λ₁ = 116`** (exactly `116.97`) and `30 + D 2^20 ≤ 2^34`. -/
theorem sharp_full_deployed :
    noForgeryRateSharp (2 ^ 20) (2 ^ 20) ≤ (2 : ℝ≥0∞)⁻¹ ^ 116 ∧
      30 + SphincsSetSharp.quadD Sphincs.Lifetimes.full * 2 ^ 20 ≤ 2 ^ 34 :=
  ⟨noForgeryRateSharp_le_of (by norm_num) (by decide), by decide⟩

end FullDeployed

section Pruned20Deployed

attribute [local instance] Sphincs.Lifetimes.pruned20

/-- **`pruned20`, `2^20 + 2^20` keys: `λ₁ = 116`** (exactly `116.12`) and
`30 + D 2^20 ≤ 2^34`. -/
theorem sharp_pruned20_deployed :
    noForgeryRateSharp (2 ^ 20) (2 ^ 20) ≤ (2 : ℝ≥0∞)⁻¹ ^ 116 ∧
      30 + SphincsSetSharp.quadD Sphincs.Lifetimes.pruned20 * 2 ^ 20 ≤ 2 ^ 34 :=
  ⟨noForgeryRateSharp_le_of (by norm_num) (by decide), by decide⟩

end Pruned20Deployed

/-- **The sharp headline at a deployed set** (`full` or `pruned20`), `2^20 + 2^20` keys:
`Pr[Breaks] ≤ q · 2^-116 + 2^34 q²/2^256`. -/
theorem aggregate_no_forgery_final_sharp_deployed [P : Sphincs.Params] [S : SphincsSetSharp P]
    (hP : noForgeryRateSharp (2 ^ 20) (2 ^ 20) ≤ (2 : ℝ≥0∞)⁻¹ ^ 116 ∧
      30 + S.quadD * 2 ^ 20 ≤ 2 ^ 34)
    (N : ℕ) (A : GameAdversary (2 ^ 20) (2 ^ 20)) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      (totalQueries (2 ^ 20) (2 ^ 20) qH sX sS N : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 116 +
        ((2 ^ 34 * totalQueries (2 ^ 20) (2 ^ 20) qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine (aggregate_no_forgery_final_sharp N A hA).trans (add_le_add ?_ ?_)
  · gcongr; exact hP.1
  · refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
    exact Nat.mul_le_mul_right _ hP.2

end LeanVM.E2E
