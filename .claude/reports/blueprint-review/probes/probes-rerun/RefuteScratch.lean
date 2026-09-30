import LeanerVM.Protocol.ToArkLib.GuardedVerdict

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

theorem not_perfectCompletenessA {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (hin : (stmtIn, witIn) ∈ relIn)
    (h : ∀ x ∈ support (reduction.run stmtIn witIn).run, ∀ result, x = some result →
      ¬ ((result.2, result.1.2.2) ∈ relOut ∧ result.1.2.1 = result.2)) :
    ¬ reduction.perfectCompleteness init impl relIn relOut := by
  intro hc
  rw [Reduction.perfectCompleteness_eq_prob_one] at hc
  have h1 := hc stmtIn witIn hin
  dsimp only at h1
  have hpos := lt_of_lt_of_eq (zero_lt_one' ℝ≥0∞) h1.symm
  rw [OracleComp.OptionT.prEvent_mk_pos_iff] at hpos
  obtain ⟨x, hx, hev⟩ := hpos
  rw [mem_support_bind_iff] at hx
  obtain ⟨s, _, hx⟩ := hx
  exact h (some x) (support_simulateQ_run'_subset _ _ s hx) x rfl hev

theorem not_perfectCompletenessB {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (hin : (stmtIn, witIn) ∈ relIn)
    (h : ∀ x ∈ support (reduction.run stmtIn witIn).run, ∀ result, x = some result →
      ¬ ((result.2, result.1.2.2) ∈ relOut ∧ result.1.2.1 = result.2)) :
    ¬ reduction.perfectCompleteness init impl relIn relOut := by
  intro hc
  rw [Reduction.perfectCompleteness_eq_prob_one] at hc
  have h1 := hc stmtIn witIn hin
  dsimp only at h1
  rw [OracleComp.OptionT.prEvent_mk_eq_one_iff] at h1
  trace_state
  sorry
