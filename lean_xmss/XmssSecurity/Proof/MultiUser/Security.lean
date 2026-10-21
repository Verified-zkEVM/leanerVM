import XmssSecurity.Proof.MultiUser.Expected

/-!
# leanXMSS, multi-user

A multi-user win names a key `j` (`gameCore_le_sum`), and the multi-user game verified under key `j`
is the single-key game of the reduction against key `j` (`forgeAdvantage_reduction`), whose budget is
`q + verifyHashBound` (`hasHashQueryBound_reduction_of`). The attributed single-key bound charges two
units per expected attributable call, and the reductions' expected attributable calls sum to at most
`q (1 + n^2 pairBound)` less the keys' own calls (`sum_expectedAttributedQueries_le`): so the
`n` single-key bounds sum to `q / 2^127`, a pair term `n^2 / 2^127` and a second-order term
`q^2 / 2^252` (`multiUser_arithmetic`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.MultiUser

open Seeded

set_option backward.isDefEq.respectTransparency false

/-! ## Arithmetic -/

/-- `2^-128`. -/
noncomputable abbrev unit128 : ℝ≥0∞ := ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹

theorem inv_two_pow_256 : ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ = unit128 * unit128 := by
  rw [show (2 ^ 256 : Nat) = 2 ^ 128 * 2 ^ 128 by norm_num, Nat.cast_mul,
    ENNReal.mul_inv (by simp) (by simp)]

theorem inv_two_pow_127 : ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ = 2 * unit128 := by
  unfold unit128
  rw [show (2 ^ 128 : Nat) = 2 * 2 ^ 127 by norm_num, Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp),
    ← mul_assoc, show ((2 : Nat) : ℝ≥0∞) = 2 by norm_num,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

theorem inv_two_pow_252 : ((2 ^ 252 : Nat) : ℝ≥0∞)⁻¹ = 16 * (unit128 * unit128) := by
  rw [← inv_two_pow_256, show (2 ^ 256 : Nat) = 16 * 2 ^ 252 by norm_num, Nat.cast_mul,
    ENNReal.mul_inv (by simp) (by simp), ← mul_assoc, show ((16 : Nat) : ℝ≥0∞) = 16 by norm_num,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

theorem natCast_mul_unit_le_one {a : Nat} (ha : a ≤ 2 ^ 128) : (a : ℝ≥0∞) * unit128 ≤ 1 := by
  calc (a : ℝ≥0∞) * unit128 ≤ ((2 ^ 128 : Nat) : ℝ≥0∞) * unit128 := by gcongr
    _ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)

theorem pairBound_le : pairBound ≤ 2 * unit128 := by
  unfold pairBound
  rw [← add_assoc, ← ENNReal.add_div, ← Nat.cast_add, two_mul]
  refine add_le_add ?_ (le_of_eq rfl)
  rw [div_eq_mul_inv, inv_two_pow_256, ← mul_assoc]
  calc ((Bridge.keygenQueries + (Bridge.keygenQueries + 1) : Nat) : ℝ≥0∞) * unit128 * unit128
      ≤ 1 * unit128 := by
        gcongr
        exact natCast_mul_unit_le_one (by rw [Bridge.keygenQueries_eq]; norm_num)
    _ = unit128 := one_mul _

/-- **The multi-user arithmetic.** -/
theorem multiUser_arithmetic (n q : Nat) (hq : q < 2 ^ 126) (hnq : n ≤ q) (hVq : verifyHashBound ≤ q)
    (sum : ℝ≥0∞)
    (hsum : sum + ((n * 2 ^ 16 : Nat) : ℝ≥0∞) ≤
      (q : ℝ≥0∞) * (1 + ((n * n : Nat) : ℝ≥0∞) * pairBound) + ((n * verifyHashBound : Nat) : ℝ≥0∞)) :
    (n : ℝ≥0∞) * (2 ^ 10 * unit128 + 4 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * 2 ^ 10 *
        (unit128 * unit128) + 2 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (unit128 * unit128)) +
      sum * (2 * unit128 + 4 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (unit128 * unit128)) ≤
    (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) + ((n ^ 2 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) +
      ((q ^ 2 : Nat) : ℝ≥0∞) / ((2 ^ 252 : Nat) : ℝ≥0∞) := by
  set u := unit128
  set X : ℝ≥0∞ := ((n * n : Nat) : ℝ≥0∞) * pairBound
  have hV : verifyHashBound = 384 := by
    simp [verifyHashBound, numChains, chainLength, winternitzBits, treeHeight]
  -- The own calls pay for the slack and one verification per key.
  have hslack : sum + (n : ℝ≥0∞) * 2 ^ 10 ≤ (q : ℝ≥0∞) * (1 + X) := by
    have hsplit : ((n * 2 ^ 16 : Nat) : ℝ≥0∞) =
        ((n * (2 ^ 16 - verifyHashBound) : Nat) : ℝ≥0∞) + ((n * verifyHashBound : Nat) : ℝ≥0∞) := by
      rw [← Nat.cast_add, ← Nat.mul_add, Nat.sub_add_cancel (by rw [hV]; norm_num)]
    rw [hsplit, ← add_assoc] at hsum
    have h := (ENNReal.add_le_add_iff_right (ENNReal.natCast_ne_top _)).mp hsum
    have hnat : n * 2 ^ 10 ≤ n * (2 ^ 16 - verifyHashBound) :=
      Nat.mul_le_mul_left _ (by rw [hV]; norm_num)
    calc sum + (n : ℝ≥0∞) * 2 ^ 10 ≤ sum + ((n * (2 ^ 16 - verifyHashBound) : Nat) : ℝ≥0∞) := by
          gcongr
          exact_mod_cast hnat
      _ ≤ _ := h
  have hq' : ((q + verifyHashBound : Nat) : ℝ≥0∞) ≤ 2 * q := by
    rw [two_mul]; push_cast; gcongr
  have h4qu : 4 * (q : ℝ≥0∞) * u ≤ 1 := by
    have := natCast_mul_unit_le_one (a := 4 * q) (by omega)
    push_cast at this
    exact this
  have h16qqu : 16 * ((q : ℝ≥0∞) * q) * (u * u) ≤ 1 := by
    have h := mul_le_mul' h4qu h4qu
    rw [one_mul] at h
    calc 16 * ((q : ℝ≥0∞) * q) * (u * u) = 4 * (q : ℝ≥0∞) * u * (4 * (q : ℝ≥0∞) * u) := by ring
      _ ≤ 1 := h
  have hX : X ≤ ((n * n : Nat) : ℝ≥0∞) * (2 * u) := mul_le_mul' le_rfl pairBound_le
  have hn : (n : ℝ≥0∞) ≤ q := by exact_mod_cast hnq
  -- Each part.
  have hpart1 : 2 * u * (sum + (n : ℝ≥0∞) * 2 ^ 9) ≤ 2 * (q : ℝ≥0∞) * u + ((n * n : Nat) : ℝ≥0∞) * u := by
    calc 2 * u * (sum + (n : ℝ≥0∞) * 2 ^ 9) ≤ 2 * u * ((q : ℝ≥0∞) * (1 + X)) := by
          gcongr
          refine le_trans ?_ hslack
          gcongr
          all_goals norm_num
      _ = 2 * (q : ℝ≥0∞) * u + 2 * (q : ℝ≥0∞) * u * X := by ring
      _ ≤ 2 * (q : ℝ≥0∞) * u + 2 * (q : ℝ≥0∞) * u * (((n * n : Nat) : ℝ≥0∞) * (2 * u)) := by gcongr
      _ = 2 * (q : ℝ≥0∞) * u + ((n * n : Nat) : ℝ≥0∞) * u * (4 * (q : ℝ≥0∞) * u) := by ring
      _ ≤ 2 * (q : ℝ≥0∞) * u + ((n * n : Nat) : ℝ≥0∞) * u * 1 := by gcongr
      _ = _ := by rw [mul_one]
  have hpart2 : 4 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (u * u) * (sum + (n : ℝ≥0∞) * 2 ^ 10) ≤
      8 * ((q : ℝ≥0∞) * q) * (u * u) + ((n * n : Nat) : ℝ≥0∞) * u := by
    calc 4 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (u * u) * (sum + (n : ℝ≥0∞) * 2 ^ 10)
        ≤ 4 * (2 * (q : ℝ≥0∞)) * (u * u) * ((q : ℝ≥0∞) * (1 + X)) := by gcongr
      _ = 8 * ((q : ℝ≥0∞) * q) * (u * u) + 8 * ((q : ℝ≥0∞) * q) * (u * u) * X := by ring
      _ ≤ 8 * ((q : ℝ≥0∞) * q) * (u * u) +
          8 * ((q : ℝ≥0∞) * q) * (u * u) * (((n * n : Nat) : ℝ≥0∞) * (2 * u)) := by gcongr
      _ = 8 * ((q : ℝ≥0∞) * q) * (u * u) +
          ((n * n : Nat) : ℝ≥0∞) * u * (16 * ((q : ℝ≥0∞) * q) * (u * u)) := by ring
      _ ≤ 8 * ((q : ℝ≥0∞) * q) * (u * u) + ((n * n : Nat) : ℝ≥0∞) * u * 1 := by gcongr
      _ = _ := by rw [mul_one]
  have hpart3 : (n : ℝ≥0∞) * (2 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (u * u)) ≤
      4 * ((q : ℝ≥0∞) * q) * (u * u) := by
    calc (n : ℝ≥0∞) * (2 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (u * u))
        ≤ (q : ℝ≥0∞) * (2 * (2 * (q : ℝ≥0∞)) * (u * u)) := by gcongr
      _ = _ := by ring
  have htarget : (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) + ((n ^ 2 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) +
      ((q ^ 2 : Nat) : ℝ≥0∞) / ((2 ^ 252 : Nat) : ℝ≥0∞) =
      2 * (q : ℝ≥0∞) * u + 2 * (((n * n : Nat) : ℝ≥0∞) * u) + 16 * ((q : ℝ≥0∞) * q) * (u * u) := by
    simp only [div_eq_mul_inv, inv_two_pow_127, inv_two_pow_252]
    push_cast
    ring
  rw [htarget]
  calc (n : ℝ≥0∞) * (2 ^ 10 * u + 4 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * 2 ^ 10 * (u * u) +
          2 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (u * u)) +
        sum * (2 * u + 4 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (u * u))
      = 2 * u * (sum + (n : ℝ≥0∞) * 2 ^ 9) +
          4 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (u * u) * (sum + (n : ℝ≥0∞) * 2 ^ 10) +
          (n : ℝ≥0∞) * (2 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (u * u)) := by ring
    _ ≤ (2 * (q : ℝ≥0∞) * u + ((n * n : Nat) : ℝ≥0∞) * u) +
          (8 * ((q : ℝ≥0∞) * q) * (u * u) + ((n * n : Nat) : ℝ≥0∞) * u) +
          4 * ((q : ℝ≥0∞) * q) * (u * u) := add_le_add (add_le_add hpart1 hpart2) hpart3
    _ ≤ 2 * (q : ℝ≥0∞) * u + 2 * (((n * n : Nat) : ℝ≥0∞) * u) + 16 * ((q : ℝ≥0∞) * q) * (u * u) := by
        have h12 : (12 : ℝ≥0∞) ≤ 16 := by norm_num
        calc (2 * (q : ℝ≥0∞) * u + ((n * n : Nat) : ℝ≥0∞) * u) +
              (8 * ((q : ℝ≥0∞) * q) * (u * u) + ((n * n : Nat) : ℝ≥0∞) * u) +
              4 * ((q : ℝ≥0∞) * q) * (u * u)
            = 2 * (q : ℝ≥0∞) * u + 2 * (((n * n : Nat) : ℝ≥0∞) * u) +
                12 * ((q : ℝ≥0∞) * q) * (u * u) := by ring
          _ ≤ _ := by gcongr

/-! ## The theorem -/

theorem single_form (E : ℝ≥0∞) (q : Nat) :
    (2 * E + 2 ^ 10) / ((2 ^ 128 : Nat) : ℝ≥0∞) + 4 * (q : ℝ≥0∞) * (E + 2 ^ 10) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
        2 * (q : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) =
      (2 ^ 10 * unit128 + 4 * (q : ℝ≥0∞) * 2 ^ 10 * (unit128 * unit128) +
        2 * (q : ℝ≥0∞) * (unit128 * unit128)) + E * (2 * unit128 + 4 * (q : ℝ≥0∞) * (unit128 * unit128)) := by
  simp only [div_eq_mul_inv, inv_two_pow_256]
  ring

-- Keep elaboration from unfolding the seed's uniform draw and key generation's literal tree.
attribute [local irreducible] LeanXmss.sampleMasterSeed LeanXmss.Seeded.keygenFromSeed
  LeanXmss.Seeded.treeNode

/-- The budget pays for every key generation. -/
theorem keygens_le_budget {n : Nat} (adversary : LeanXmss.MultiUser.Adversary n) (q : Nat)
    (hbound : LeanXmss.MultiUser.HasHashQueryBound adversary q) : n * Bridge.keygenQueries ≤ q := by
  obtain ⟨y, hy⟩ := probComp_support_nonempty (romRun (tracedPrefix adversary) ∅)
  have hlen := prefix_length_le adversary q hbound y hy
  obtain ⟨parts, hparts, hpartsEq⟩ := tracedPrefix_parts adversary ∅ y hy
  have hslot : ∀ i, (y.1.1 i).2.length = Bridge.keygenQueries := by
    intro i
    obtain ⟨start, finish, hmem⟩ := mem_support_sequenceFin _ ∅ parts hparts i
    rw [hpartsEq] at hmem
    exact length_trace_keygen start _ hmem
  rw [length_flatTrace] at hlen
  simp only [hslot, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlen
  omega

theorem forgeAdvantage_eq {n : Nat} (adversary : LeanXmss.MultiUser.Adversary n) :
    LeanXmss.MultiUser.forgeAdvantage adversary =
      Pr{let x ← (simulateQ romImpl (LeanXmss.MultiUser.gameCore adversary :
        OracleComp OracleWorld Bool)).run' ∅}[x = true] := by
  unfold LeanXmss.MultiUser.forgeAdvantage LeanXmss.MultiUser.experiment
  rw [← Bridge.probOutput_countHashQueries, simulateQ_countHashQueries]
  rfl

/-- **leanXMSS, multi-user.** -/
theorem leanXmss_multiUserSecurity : LeanXmss.LeanXmssMultiUserSecurityStatement := by
  intro n q hq adversary hbound
  have hK := keygens_le_budget adversary q hbound
  rw [forgeAdvantage_eq]
  refine (gameCore_le_sum adversary).trans ?_
  simp only [← forgeAdvantage_reduction]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hKval := Bridge.keygenQueries_eq
  have hV : verifyHashBound = 384 := by
    simp [verifyHashBound, numChains, chainLength, winternitzBits, treeHeight]
  have hnq : n ≤ q := by
    calc n ≤ n * Bridge.keygenQueries := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ q := hK
  have hVq : verifyHashBound ≤ q := by
    calc verifyHashBound ≤ n * Bridge.keygenQueries := by
          rw [hV, hKval]; exact le_trans (by norm_num) (Nat.mul_le_mul_right _ hn)
      _ ≤ q := hK
  calc ∑ j, LeanXmss.Security.forgeAdvantage (reduction adversary j)
      ≤ ∑ j, ((2 ^ 10 * unit128 + 4 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * 2 ^ 10 *
          (unit128 * unit128) + 2 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (unit128 * unit128)) +
          LeanXmss.Security.expectedAttributedQueries (reduction adversary j) *
            (2 * unit128 + 4 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (unit128 * unit128))) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← single_form]
        exact Bridge.leanXmss_attributedSecurity (q + verifyHashBound) (by rw [hV]; omega)
          (reduction adversary j) (hasHashQueryBound_reduction_of adversary j q hbound)
    _ = (n : ℝ≥0∞) * (2 ^ 10 * unit128 + 4 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * 2 ^ 10 *
          (unit128 * unit128) + 2 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (unit128 * unit128)) +
          (∑ j, LeanXmss.Security.expectedAttributedQueries (reduction adversary j)) *
            (2 * unit128 + 4 * ((q + verifyHashBound : Nat) : ℝ≥0∞) * (unit128 * unit128)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.sum_mul]
    _ ≤ _ := multiUser_arithmetic n q (by omega) hnq hVq _
        (sum_expectedAttributedQueries_le adversary q hbound)

end XmssSecurity.MultiUser
