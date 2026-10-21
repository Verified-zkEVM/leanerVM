import Sphincs.LifetimesMulti
import Sphincs.MultiBound

/-! **The multi-user bound paid per key, at every proved lifetime.** From the certificates of each
parameter set (`LifetimesMulti`), against `n` keys every adversary whose experiment makes at most
`q ≥ 1` hash calls wins with probability at most `Multi.multiBound`: for `2 (q + 307) − keygenCost`
within the small-route certificate, `ρ / 2^128 / (1 − 2 (q + 307) ρ / 2^128)` times
`q (1 + n² pairChance) + n (309 + ...)`, plus `n` times the cover, coin, near and seed terms at the
budget `2 (q + 307)` (`Multi.multiSmall`), and never more than `n q / 2^127`. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Lifetimes

open Security ForsPotential

/-- **`n` keys at subtree height 26**, paid per key. -/
theorem full_multiUserKey (n : ℕ) :
    @Multi.HasMultiUserBound full n (@Multi.multiBound full n 250752950924986904089568310569467904 (H0.rho_b26 : ℝ) H0.small_b26.B
      ((2 - H0.rho_b26 + ((250752950924986904089568310569467904 : ℕ) : ℚ) / 2 ^ 128 + ((1383000000 : ℕ) : ℚ) * 123 / (2 ^ 26 * 2 ^ 15)) * ((2 ^ 26 * H0.near_b26.En : ℚ) / 2))) :=
  @Multi.hasMultiUserBound_multiBound full (by decide) 26 1383000000 rfl rfl 250752950924986904089568310569467904 H0.rho_b26 H0.tab_b26 H0.small_b26
    H0.near_b26 H0.tab_b26_ok H0.rate_b26_ok H0.small_b26_ok H0.near_b26_ok H0.check_b26_ok
    full_bitsBudgeted n

/-- **`n` keys at subtree height 20**, paid per key. -/
theorem pruned20_multiUserKey (n : ℕ) :
    @Multi.HasMultiUserBound pruned20 n (@Multi.multiBound pruned20 n 558871528355207643822193711415033856 (H0.rho_b20 : ℝ) H0.small_b20.B
      ((2 - H0.rho_b20 + ((558871528355207643822193711415033856 : ℕ) : ℚ) / 2 ^ 128 + ((26030000 : ℕ) : ℚ) * 123 / (2 ^ 20 * 2 ^ 15)) * ((2 ^ 20 * H0.near_b20.En : ℚ) / 2))) :=
  @Multi.hasMultiUserBound_multiBound pruned20 (by decide) 20 26030000 rfl rfl 558871528355207643822193711415033856 H0.rho_b20 H0.tab_b20 H0.small_b20
    H0.near_b20 H0.tab_b20_ok H0.rate_b20_ok H0.small_b20_ok H0.near_b20_ok H0.check_b20_ok
    pruned20_bitsBudgeted n

/-- **`n` keys at subtree height 14**, paid per key. -/
theorem pruned14_multiUserKey (n : ℕ) :
    @Multi.HasMultiUserBound pruned14 n (@Multi.multiBound pruned14 n 1179940068462340716375613534384422912 (H0.rho_b14 : ℝ) H0.small_b14.B
      ((2 - H0.rho_b14 + ((1179940068462340716375613534384422912 : ℕ) : ℚ) / 2 ^ 128 + ((480900 : ℕ) : ℚ) * 123 / (2 ^ 14 * 2 ^ 15)) * ((2 ^ 14 * H0.near_b14.En : ℚ) / 2))) :=
  @Multi.hasMultiUserBound_multiBound pruned14 (by decide) 14 480900 rfl rfl 1179940068462340716375613534384422912 H0.rho_b14 H0.tab_b14 H0.small_b14
    H0.near_b14 H0.tab_b14_ok H0.rate_b14_ok H0.small_b14_ok H0.near_b14_ok H0.check_b14_ok
    pruned14_bitsBudgeted n

/-- **`n` keys at subtree height 13**, paid per key. -/
theorem pruned13_multiUserKey (n : ℕ) :
    @Multi.HasMultiUserBound pruned13 n (@Multi.multiBound pruned13 n 1314909569352122321482228451418046464 (H0.rho_b13 : ℝ) H0.small_b13.B
      ((2 - H0.rho_b13 + ((1314909569352122321482228451418046464 : ℕ) : ℚ) / 2 ^ 128 + ((247000 : ℕ) : ℚ) * 123 / (2 ^ 13 * 2 ^ 15)) * ((2 ^ 13 * H0.near_b13.En : ℚ) / 2))) :=
  @Multi.hasMultiUserBound_multiBound pruned13 (by decide) 13 247000 rfl rfl 1314909569352122321482228451418046464 H0.rho_b13 H0.tab_b13 H0.small_b13
    H0.near_b13 H0.tab_b13_ok H0.rate_b13_ok H0.small_b13_ok H0.near_b13_ok H0.check_b13_ok
    pruned13_bitsBudgeted n

/-- **`n` keys at subtree height 12**, paid per key. -/
theorem pruned12_multiUserKey (n : ℕ) :
    @Multi.HasMultiUserBound pruned12 n (@Multi.multiBound pruned12 n 1449533407878593313898110627080044544 (H0.rho_b12 : ℝ) H0.small_b12.B
      ((2 - H0.rho_b12 + ((1449533407878593313898110627080044544 : ℕ) : ℚ) / 2 ^ 128 + ((126900 : ℕ) : ℚ) * 123 / (2 ^ 12 * 2 ^ 15)) * ((2 ^ 12 * H0.near_b12.En : ℚ) / 2))) :=
  @Multi.hasMultiUserBound_multiBound pruned12 (by decide) 12 126900 rfl rfl 1449533407878593313898110627080044544 H0.rho_b12 H0.tab_b12 H0.small_b12
    H0.near_b12 H0.tab_b12_ok H0.rate_b12_ok H0.small_b12_ok H0.near_b12_ok H0.check_b12_ok
    pruned12_bitsBudgeted n

/-- **`n` keys at subtree height 10**, paid per key. -/
theorem pruned10_multiUserKey (n : ℕ) :
    @Multi.HasMultiUserBound pruned10 n (@Multi.multiBound pruned10 n 1742566343746827758207774509045383168 (H0.rho_b10 : ℝ) H0.small_b10.B
      ((2 - H0.rho_b10 + ((1742566343746827758207774509045383168 : ℕ) : ℚ) / 2 ^ 128 + ((33490 : ℕ) : ℚ) * 123 / (2 ^ 10 * 2 ^ 15)) * ((2 ^ 10 * H0.near_b10.En : ℚ) / 2))) :=
  @Multi.hasMultiUserBound_multiBound pruned10 (by decide) 10 33490 rfl rfl 1742566343746827758207774509045383168 H0.rho_b10 H0.tab_b10 H0.small_b10
    H0.near_b10 H0.tab_b10_ok H0.rate_b10_ok H0.small_b10_ok H0.near_b10_ok H0.check_b10_ok
    pruned10_bitsBudgeted n

/-- **`n` keys at subtree height 8**, paid per key. -/
theorem pruned8_multiUserKey (n : ℕ) :
    @Multi.HasMultiUserBound pruned8 n (@Multi.multiBound pruned8 n 2027867772287336761555281578532274176 (H0.rho_b8 : ℝ) H0.small_b8.B
      ((2 - H0.rho_b8 + ((2027867772287336761555281578532274176 : ℕ) : ℚ) / 2 ^ 128 + ((8830 : ℕ) : ℚ) * 123 / (2 ^ 8 * 2 ^ 15)) * ((2 ^ 8 * H0.near_b8.En : ℚ) / 2))) :=
  @Multi.hasMultiUserBound_multiBound pruned8 (by decide) 8 8830 rfl rfl 2027867772287336761555281578532274176 H0.rho_b8 H0.tab_b8 H0.small_b8
    H0.near_b8 H0.tab_b8_ok H0.rate_b8_ok H0.small_b8_ok H0.near_b8_ok H0.check_b8_ok
    pruned8_bitsBudgeted n

/-- **The forest lifetimes with `n` keys, paid per key**, at every subtree height. -/
theorem requestedMultiUserKey (n : ℕ) :
    @Multi.HasMultiUserBound full n (@Multi.multiBound full n 250752950924986904089568310569467904 (H0.rho_b26 : ℝ) H0.small_b26.B
      ((2 - H0.rho_b26 + ((250752950924986904089568310569467904 : ℕ) : ℚ) / 2 ^ 128 + ((1383000000 : ℕ) : ℚ) * 123 / (2 ^ 26 * 2 ^ 15)) * ((2 ^ 26 * H0.near_b26.En : ℚ) / 2))) ∧
    @Multi.HasMultiUserBound pruned20 n (@Multi.multiBound pruned20 n 558871528355207643822193711415033856 (H0.rho_b20 : ℝ) H0.small_b20.B
      ((2 - H0.rho_b20 + ((558871528355207643822193711415033856 : ℕ) : ℚ) / 2 ^ 128 + ((26030000 : ℕ) : ℚ) * 123 / (2 ^ 20 * 2 ^ 15)) * ((2 ^ 20 * H0.near_b20.En : ℚ) / 2))) ∧
    @Multi.HasMultiUserBound pruned14 n (@Multi.multiBound pruned14 n 1179940068462340716375613534384422912 (H0.rho_b14 : ℝ) H0.small_b14.B
      ((2 - H0.rho_b14 + ((1179940068462340716375613534384422912 : ℕ) : ℚ) / 2 ^ 128 + ((480900 : ℕ) : ℚ) * 123 / (2 ^ 14 * 2 ^ 15)) * ((2 ^ 14 * H0.near_b14.En : ℚ) / 2))) ∧
    @Multi.HasMultiUserBound pruned13 n (@Multi.multiBound pruned13 n 1314909569352122321482228451418046464 (H0.rho_b13 : ℝ) H0.small_b13.B
      ((2 - H0.rho_b13 + ((1314909569352122321482228451418046464 : ℕ) : ℚ) / 2 ^ 128 + ((247000 : ℕ) : ℚ) * 123 / (2 ^ 13 * 2 ^ 15)) * ((2 ^ 13 * H0.near_b13.En : ℚ) / 2))) ∧
    @Multi.HasMultiUserBound pruned12 n (@Multi.multiBound pruned12 n 1449533407878593313898110627080044544 (H0.rho_b12 : ℝ) H0.small_b12.B
      ((2 - H0.rho_b12 + ((1449533407878593313898110627080044544 : ℕ) : ℚ) / 2 ^ 128 + ((126900 : ℕ) : ℚ) * 123 / (2 ^ 12 * 2 ^ 15)) * ((2 ^ 12 * H0.near_b12.En : ℚ) / 2))) ∧
    @Multi.HasMultiUserBound pruned10 n (@Multi.multiBound pruned10 n 1742566343746827758207774509045383168 (H0.rho_b10 : ℝ) H0.small_b10.B
      ((2 - H0.rho_b10 + ((1742566343746827758207774509045383168 : ℕ) : ℚ) / 2 ^ 128 + ((33490 : ℕ) : ℚ) * 123 / (2 ^ 10 * 2 ^ 15)) * ((2 ^ 10 * H0.near_b10.En : ℚ) / 2))) ∧
    @Multi.HasMultiUserBound pruned8 n (@Multi.multiBound pruned8 n 2027867772287336761555281578532274176 (H0.rho_b8 : ℝ) H0.small_b8.B
      ((2 - H0.rho_b8 + ((2027867772287336761555281578532274176 : ℕ) : ℚ) / 2 ^ 128 + ((8830 : ℕ) : ℚ) * 123 / (2 ^ 8 * 2 ^ 15)) * ((2 ^ 8 * H0.near_b8.En : ℚ) / 2))) :=
  ⟨full_multiUserKey n, pruned20_multiUserKey n, pruned14_multiUserKey n, pruned13_multiUserKey n, pruned12_multiUserKey n, pruned10_multiUserKey n, pruned8_multiUserKey n⟩

end Sphincs.Lifetimes
