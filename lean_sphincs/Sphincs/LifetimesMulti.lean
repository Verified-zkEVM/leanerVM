import Sphincs.Lifetimes
import Sphincs.MultiReduction

/-! **Budgeted and multi-user forms of the proved lifetimes.** Each parameter set of `Lifetimes`
bounds the probability of a win within `q` hash calls by `q / 2^127` for every adversary
(`Det.HasClassicalSecurityBitsDetBudgeted`), from the same certificates. With `n` keys
(`StatementMulti`), the multi-user experiment's advantage is at most `n q / 2^127`
(`Multi.hasMultiUserBound_of_budgeted`). -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Lifetimes

open Security ForsPotential

/-- **127 bits within the budget** at subtree height 26 and 1383000000 signatures. -/
theorem full_bitsBudgeted : @Det.HasClassicalSecurityBitsDetBudgeted full 127 :=
  @det_bitsFH_budgeted full (by decide) 26 1383000000 rfl rfl 250752950924986904089568310569467904 H0.rho_b26 H0.tab_b26 H0.small_b26 H0.near_b26 H0.tab_b26_ok
    H0.rate_b26_ok H0.small_b26_ok H0.near_b26_ok H0.check_b26_ok [H0.cover_b26_0] [] H0.covers_b26_ok

/-- **127 bits within the budget** at subtree height 20 and 26030000 signatures. -/
theorem pruned20_bitsBudgeted : @Det.HasClassicalSecurityBitsDetBudgeted pruned20 127 :=
  @det_bitsFH_budgeted pruned20 (by decide) 20 26030000 rfl rfl 558871528355207643822193711415033856 H0.rho_b20 H0.tab_b20 H0.small_b20 H0.near_b20 H0.tab_b20_ok
    H0.rate_b20_ok H0.small_b20_ok H0.near_b20_ok H0.check_b20_ok [H0.cover_b20_0, H0.cover_b20_1] [H0.coverh_b20_0] H0.covers_b20_ok

/-- **127 bits within the budget** at subtree height 14 and 480900 signatures. -/
theorem pruned14_bitsBudgeted : @Det.HasClassicalSecurityBitsDetBudgeted pruned14 127 :=
  @det_bitsFH_budgeted pruned14 (by decide) 14 480900 rfl rfl 1179940068462340716375613534384422912 H0.rho_b14 H0.tab_b14 H0.small_b14 H0.near_b14 H0.tab_b14_ok
    H0.rate_b14_ok H0.small_b14_ok H0.near_b14_ok H0.check_b14_ok [H0.cover_b14_0, H0.cover_b14_1] [H0.coverh_b14_0] H0.covers_b14_ok

/-- **127 bits within the budget** at subtree height 13 and 247000 signatures. -/
theorem pruned13_bitsBudgeted : @Det.HasClassicalSecurityBitsDetBudgeted pruned13 127 :=
  @det_bitsFH_budgeted pruned13 (by decide) 13 247000 rfl rfl 1314909569352122321482228451418046464 H0.rho_b13 H0.tab_b13 H0.small_b13 H0.near_b13 H0.tab_b13_ok
    H0.rate_b13_ok H0.small_b13_ok H0.near_b13_ok H0.check_b13_ok [H0.cover_b13_0, H0.cover_b13_1] [H0.coverh_b13_0] H0.covers_b13_ok

/-- **127 bits within the budget** at subtree height 12 and 126900 signatures. -/
theorem pruned12_bitsBudgeted : @Det.HasClassicalSecurityBitsDetBudgeted pruned12 127 :=
  @det_bitsFH_budgeted pruned12 (by decide) 12 126900 rfl rfl 1449533407878593313898110627080044544 H0.rho_b12 H0.tab_b12 H0.small_b12 H0.near_b12 H0.tab_b12_ok
    H0.rate_b12_ok H0.small_b12_ok H0.near_b12_ok H0.check_b12_ok [H0.cover_b12_0, H0.cover_b12_1] [H0.coverh_b12_0] H0.covers_b12_ok

/-- **127 bits within the budget** at subtree height 10 and 33490 signatures. -/
theorem pruned10_bitsBudgeted : @Det.HasClassicalSecurityBitsDetBudgeted pruned10 127 :=
  @det_bitsFH_budgeted pruned10 (by decide) 10 33490 rfl rfl 1742566343746827758207774509045383168 H0.rho_b10 H0.tab_b10 H0.small_b10 H0.near_b10 H0.tab_b10_ok
    H0.rate_b10_ok H0.small_b10_ok H0.near_b10_ok H0.check_b10_ok [H0.cover_b10_0, H0.cover_b10_1] [H0.coverh_b10_0] H0.covers_b10_ok

/-- **127 bits within the budget** at subtree height 8 and 8830 signatures. -/
theorem pruned8_bitsBudgeted : @Det.HasClassicalSecurityBitsDetBudgeted pruned8 127 :=
  @det_bitsFH_budgeted pruned8 (by decide) 8 8830 rfl rfl 2027867772287336761555281578532274176 H0.rho_b8 H0.tab_b8 H0.small_b8 H0.near_b8 H0.tab_b8_ok
    H0.rate_b8_ok H0.small_b8_ok H0.near_b8_ok H0.check_b8_ok [H0.cover_b8_0, H0.cover_b8_1] [H0.coverh_b8_0] H0.covers_b8_ok

/-- **The forest lifetimes within the budget**: 127 bits at every subtree height, no query bound
assumed. -/
theorem requestedSecurityBudgeted :
    @Det.HasClassicalSecurityBitsDetBudgeted full 127 ∧
    @Det.HasClassicalSecurityBitsDetBudgeted pruned20 127 ∧
    @Det.HasClassicalSecurityBitsDetBudgeted pruned14 127 ∧
    @Det.HasClassicalSecurityBitsDetBudgeted pruned13 127 ∧
    @Det.HasClassicalSecurityBitsDetBudgeted pruned12 127 ∧
    @Det.HasClassicalSecurityBitsDetBudgeted pruned10 127 ∧
    @Det.HasClassicalSecurityBitsDetBudgeted pruned8 127 :=
  ⟨full_bitsBudgeted, pruned20_bitsBudgeted, pruned14_bitsBudgeted, pruned13_bitsBudgeted, pruned12_bitsBudgeted, pruned10_bitsBudgeted, pruned8_bitsBudgeted⟩

/-- **The forest lifetimes with `n` keys**: against `n` keys, every adversary whose experiment makes
at most `q ≥ 1` hash calls wins with probability at most `n q / 2^127`, at every subtree height. -/
theorem requestedMultiUser (n : ℕ) :
    @Multi.HasMultiUserBound full n (fun q => n * (q / ((2 ^ 127 : ℕ) : ℝ≥0∞))) ∧
    @Multi.HasMultiUserBound pruned20 n (fun q => n * (q / ((2 ^ 127 : ℕ) : ℝ≥0∞))) ∧
    @Multi.HasMultiUserBound pruned14 n (fun q => n * (q / ((2 ^ 127 : ℕ) : ℝ≥0∞))) ∧
    @Multi.HasMultiUserBound pruned13 n (fun q => n * (q / ((2 ^ 127 : ℕ) : ℝ≥0∞))) ∧
    @Multi.HasMultiUserBound pruned12 n (fun q => n * (q / ((2 ^ 127 : ℕ) : ℝ≥0∞))) ∧
    @Multi.HasMultiUserBound pruned10 n (fun q => n * (q / ((2 ^ 127 : ℕ) : ℝ≥0∞))) ∧
    @Multi.HasMultiUserBound pruned8 n (fun q => n * (q / ((2 ^ 127 : ℕ) : ℝ≥0∞))) :=
  ⟨@Multi.hasMultiUserBound_of_budgeted full 127 full_bitsBudgeted n, @Multi.hasMultiUserBound_of_budgeted pruned20 127 pruned20_bitsBudgeted n, @Multi.hasMultiUserBound_of_budgeted pruned14 127 pruned14_bitsBudgeted n, @Multi.hasMultiUserBound_of_budgeted pruned13 127 pruned13_bitsBudgeted n, @Multi.hasMultiUserBound_of_budgeted pruned12 127 pruned12_bitsBudgeted n, @Multi.hasMultiUserBound_of_budgeted pruned10 127 pruned10_bitsBudgeted n, @Multi.hasMultiUserBound_of_budgeted pruned8 127 pruned8_bitsBudgeted n⟩

end Sphincs.Lifetimes
