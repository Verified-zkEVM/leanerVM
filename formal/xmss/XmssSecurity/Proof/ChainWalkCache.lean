import XmssSecurity.Proof.ChainOraclePresampling

open OracleComp OracleSpec

namespace XmssSecurity

theorem simulate_chainWalk_run_eq_pure_of_table_matches
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (hseeds : ChainTableSeedsMatch secretKey chain table)
    (hedges : ChainTableEdgesMatch cache secretKey.parameter chain table)
    (leafIndex : LeafIndex) : ∀ (steps : Nat) (hsteps : steps < chainLength),
    (simulateQ randomOracle
      (Concrete.chainWalk secretKey.parameter leafIndex chain 0 steps
        (secretKey.chainStart leafIndex chain))).run cache =
      pure (table (leafIndex, ⟨steps, hsteps⟩), cache) := by
  intro steps
  induction steps with
  | zero =>
      intro hsteps
      simp [Concrete.chainWalk, hseeds leafIndex]
  | succ steps ih =>
      intro hsteps
      have hprevious : steps < chainLength := by omega
      have hedgeStep : steps < chainLength - 1 := by omega
      rw [Concrete.chainWalk, simulateQ_bind, StateT.run_bind,
        ih hprevious]
      simp only [pure_bind]
      split
      · rename_i hvalid
        simp only [zero_add] at hvalid ⊢
        let edge : ChainEdgeIndex := (leafIndex, ⟨steps, hedgeStep⟩)
        obtain ⟨output, hcached, htruncate⟩ := hedges edge
        let input := chainTableEdgeInput
          secretKey.parameter chain table edge
        change (fun result : HashOutput × QueryCache HashSpec =>
          (truncateHash result.1, result.2)) <$>
            (randomOracle input).run cache = _
        rw [randomOracle, QueryImpl.withCaching_run_some _ hcached]
        simp [htruncate, chainTableEdgeTarget, chainStepNextDigit, edge]
      · rename_i hinvalid
        omega


end XmssSecurity
