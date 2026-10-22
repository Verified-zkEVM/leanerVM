import LeanVM.E2E.SanityDeployed.Count
import LeanVM.E2E.Headline

/-!
# S1 with V_I's budget

`sanity_deployed` runs V_I without a budget. The soundness game runs it with the budgeted hash
`budgetedQuery budget` (a query while fewer than `budget` were made, a rejection past it), on `N`
nodes from the signers' initial state, with the headline's budget `viCost N = N · viNodeCost`.
Here V_I runs as the game runs it, its hash queries answered by BLAKE2s (any simulation `impl`
answering every hash query `x` with `blake2sBytes x`, e.g. `hashImplOf blake2sBytes`):

* the deployed honest proof costs V_I at most `viCost N` queries on `N ≥ T.size` nodes
  (`queryCount_deployed_le_mul`, `SanityDeployed/Count.lean`: `134,742,095` per node and
  `13,508` at the root, within the H-oblivious prover's `viNodeBound = viNodeCost`), whatever the
  rows, so `viCost` covers both honest provers unchanged;
* so the budgeted run is V_I's run with BLAKE2s, `spent` advanced by its count
  (`run_idealVerify_budgetedQuery_of_le`), which accepts unless a BLAKE2s compression collision
  occurs (`sanity_deployed`).

**`sanity_deployed_budget`**: for an honest tree valid at BLAKE2s within the deployed limits, the
deployed honest prover's output has the tree's claims, passes the deployed outer verifier, costs
V_I at most `viCost N`, and the game's budgeted V_I on `N` nodes from `SignState.init` accepts it
with `spent` its query count, or a compression collision exists. `sanity_deployed_budget_of_tree`
adds the prover's output from the proofs of work being found.
-/

namespace LeanVM.E2E.SanityDeployed

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.LeanIsa
open LeanVM.Guest LeanVM.E2E.Complete LeanVM.E2E.Sanity OracleComp OracleSpec

/-- **`viCost N` covers the deployed honest proof**: V_I with BLAKE2s on `N` nodes makes at most
`viCost N` queries on the deployed honest idealized proof of a tree of at most `N` nodes within
the deployed limits. -/
theorem queryCount_deployed_le_viCost {ρ pfuel : ℕ} (hρ : validRate ρ) {T : HonestTree}
    (hlim : T.WithinLimitsDep ρ pfuel) {s : Node.NodeStatement} {π : Proof} {ip : IdealProof}
    (hout : deployedProve ρ pfuel T = some (s, π, ip)) {N : ℕ} (hN : T.size ≤ N) :
    queryCount blake2sBytes guest ip N s ≤ viCost N := by
  rw [viCost, viNodeCost_eq]
  exact queryCount_deployed_le_mul ρ pfuel hρ hlim hout hN

/-- **S1 with V_I's budget.** For an honest witness tree `T` valid at BLAKE2s and within the
deployed limits, a valid rate, and the deployed honest prover's output `(s, π, ip)`: the statement
has the tree's claims, the deployed outer verifier accepts it, V_I with BLAKE2s makes at most
`viCost N` queries on `N ≥ T.size` nodes, and V_I run as the game runs it (`budgetedQuery
(viCost N)`, fuel `N`, from `SignState.init`), its hash queries answered by BLAKE2s, accepts with
`spent` its query count, unless a BLAKE2s compression collision occurs. -/
theorem sanity_deployed_budget {nx ns : ℕ} {b : Type → Type} [Monad b] [LawfulMonad b]
    (impl : QueryImpl GameSpec b)
    (himpl : ∀ x, simulateQ impl (liftM (HashSpec.query x) : OracleComp GameSpec Digest) =
      pure (blake2sBytes x))
    (ρ pfuel : ℕ) (T : HonestTree) (hρ : validRate ρ) (hv : T.Valid blake2sBytes)
    (hlim : T.WithinLimitsDep ρ pfuel) {s : Node.NodeStatement} {π : Proof} {ip : IdealProof}
    (hout : deployedProve ρ pfuel T = some (s, π, ip)) {N : ℕ} (hN : T.size ≤ N) :
    s.claims = T.claims ∧ Node.verifyAggregate guest s π ∧
      queryCount blake2sBytes guest ip N s ≤ viCost N ∧
      (simulateQ impl (((idealVerify (budgetedQuery (viCost N)) guest ip N s).run).run
          (SignState.init nx ns)) =
        pure (some true,
          { SignState.init nx ns with spent := queryCount blake2sBytes guest ip N s }) ∨
        CompressionCollision) := by
  obtain ⟨hcl, hagg, hV⟩ := sanity_deployed ρ pfuel T hρ hv hout hN
  have hq := queryCount_deployed_le_viCost hρ hlim hout hN
  refine ⟨hcl, hagg, hq, hV.imp (fun hacc ↦ ?_) id⟩
  have hb : (SignState.init nx ns).spent + queryCount blake2sBytes guest ip N s ≤ viCost N := by
    simpa [SignState.init] using hq
  rw [run_idealVerify_budgetedQuery_of_le impl blake2sBytes himpl hb]
  simp only [SignState.init, Nat.zero_add]
  exact congrArg (fun v ↦ pure (some v, _)) hacc

/-- **S1 with V_I's budget, from the tree's conditions**: validity, the deployed limits and
budget, the proofs of work found within `pfuel`, at a valid rate; the deployed honest prover
outputs, and its output passes as in `sanity_deployed_budget`. -/
theorem sanity_deployed_budget_of_tree {nx ns : ℕ} {b : Type → Type} [Monad b] [LawfulMonad b]
    (impl : QueryImpl GameSpec b)
    (himpl : ∀ x, simulateQ impl (liftM (HashSpec.query x) : OracleComp GameSpec Digest) =
      pure (blake2sBytes x))
    (ρ pfuel : ℕ) (T : HonestTree) (hρ : validRate ρ) (hv : T.Valid blake2sBytes)
    (hlim : T.WithinLimitsDep ρ pfuel) (hpow : T.PowFoundDep ρ pfuel) {N : ℕ}
    (hN : T.size ≤ N) :
    ∃ s π ip, deployedProve ρ pfuel T = some (s, π, ip) ∧ s.claims = T.claims ∧
      Node.verifyAggregate guest s π ∧ queryCount blake2sBytes guest ip N s ≤ viCost N ∧
      (simulateQ impl (((idealVerify (budgetedQuery (viCost N)) guest ip N s).run).run
          (SignState.init nx ns)) =
        pure (some true,
          { SignState.init nx ns with spent := queryCount blake2sBytes guest ip N s }) ∨
        CompressionCollision) := by
  obtain ⟨s, π, ip, h⟩ := deployedProve_isSome ρ pfuel hρ T hv hlim hpow
  exact ⟨s, π, ip, h, sanity_deployed_budget impl himpl ρ pfuel T hρ hv hlim h hN⟩

end LeanVM.E2E.SanityDeployed
