import SphincsBase.Proof.Base.Prelude
import SphincsBase.Proof.Chains.AdaptiveChainObservation
import SphincsBase.Proof.Chains.PartialChainLikelihoodLower
namespace SphincsBase.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expectation_bind {First Second : Type} (prior : PMF First) (next : First → PMF Second)
    (payoff : Second → ENNReal) :
    (∑' result, prior.bind next result * payoff result) =
      ∑' first, prior first * ∑' result, next first result * payoff result := by
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

theorem expectation_map {First Second : Type} (prior : PMF First) (next : First → Second)
    (payoff : Second → ENNReal) :
    (∑' result, prior.map next result * payoff result) = ∑' first, prior first * payoff (next first) := by
  rw [← PMF.bind_pure_comp, expectation_bind]
  refine tsum_congr fun first => ?_
  simp [PMF.pure_apply]

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat}

theorem run_weighted_payoff {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (payoff : Result × (Fin n → State → Option State) → ENNReal) :
    (∑' tables, completeTables observed tables * ∑' result, observedRun auxiliary tables computation observed result *
      ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) * payoff result)) =
        ∑' result, lazyRun auxiliary computation observed result * (meanPreimages result.2 endpoint * payoff result) := by
  have h := congrArg (fun law : PMF ((Fin n → State → State) × (Result × (Fin n → State → Option State))) =>
    ∑' result, law result * ((EndpointPreimageDensity.preimages evaluate result.1 endpoint : ENNReal) * payoff result.2))
    (run_posterior auxiliary computation observed)
  simp only [expectation_bind, expectation_map] at h
  rw [h]
  apply tsum_congr
  intro result
  congr 1
  simp only [meanPreimages, ← mul_assoc, ENNReal.tsum_mul_right]

end SphincsBase.Concrete.PartialChainEndpoint
