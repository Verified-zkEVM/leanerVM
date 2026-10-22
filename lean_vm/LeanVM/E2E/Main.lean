import LeanVM.E2E.Headline
import LeanVM.E2E.HeadlineSharp
import LeanVM.E2E.Sanity
import LeanVM.E2E.SanityDeployed
import LeanVM.E2E.SanityDeployedBudget

/-!
# The end-to-end security of leanVM aggregation: the result

This file states the whole end-to-end result in six theorems; every other theorem under
`LeanVM/E2E/` is a step of their proofs. The design is `docs/roadmap/e2e-security.md` (§0 the claim,
§7 the decisions), `docs/roadmap/headline.md` (the form of the bound).

## The model

* **The oracle.** One byte-level random oracle `H : Bytes → Digest`, lazily sampled
  (`Rom.loggedRO`), shared by every party: the adversary, the honest signers and the verifier.
* **The verifier.** `V_I` (`idealVerify`, `LeanVM/E2E/Statement.lean`) is the idealized,
  non-succinct verifier of an aggregation tree: from a root statement and an idealized proof (a
  partial word and frames per node, decision E2E-10) it runs the deployed outer verifier's checks
  with the oracle, decodes every node's children from its stack, and visits at most `N` nodes with
  at most `viCost N` oracle queries (`budgetedQuery`), `viCost N = 179,733,089 · N`.
* **The game.** `game guest N (viCost N) A` (`LeanVM/E2E/Statement.lean`): honest keys, `n_x`
  leanXMSS and `n_s` leanSPHINCS, generated from uniform seeds in the oracle; the adversary `A`
  receives their public keys, queries the oracle and the honest signers (a leanXMSS key refuses a
  reused leaf, a leanSPHINCS key its `signatureLimit`), and outputs a root statement and an
  idealized proof; `V_I` checks them.
* **The event.** `Breaks`: `V_I` accepts and the root statement holds a claim `(pk_j, m)` of an
  honest key on a message no request to that key was answered for, or a DA claim whose codeword
  rows the oracle's log does not back.
* **The count.** `q = totalQueries n_x n_s qH sX sS N` is every hash evaluation of the game: the
  key generations, the adversary's `qH` queries, the `sX` leanXMSS and `sS` leanSPHINCS signatures
  it requests at their proved worst-case costs, and `viCost N` (`totalQueries_eq`).

## The results

1. **No forgery** (`no_forgery`): `Pr[Breaks] ≤ q · 2^-λ₁ + 30 q²/2^256` for every parameter set,
   every number of keys and every adversary, no cap on `q`; `λ₁ ≈ 127 − log₂(n_s + 1.53)`, `106` at
   `2^20 + 2^20` keys, `126` with leanXMSS keys only.
2. **No forgery, sharp** (`no_forgery_sharp`, `no_forgery_sharp_deployed`): with leanSPHINCS's
   per-key multi-user bound, `q · 2^-λ₁ + (30 + D n_s) q²/2^256`; `q · 2^-116 + 2^34 q²/2^256` at
   `2^20 + 2^20` keys for the deployed sets `full` and `pruned20`.
3. **Completeness** (`complete`): the honest prover's proof of any generated valid tree is rejected
   by the game's `V_I` (same oracle, same budget, same fuel) with probability at most
   `completeError (QG + QP) pfuel`; `2^-124` at the honest leanXMSS leaf.
4. **Sanity** (`sanity`, T7″): `V_I` with BLAKE2s for the oracle accepts what the deployed
   aggregation accepts, when the reached nodes' partial words encode known stacks.
5. **Sanity, deployed** (`sanity_deployed`, S1): the deployed honest prover's output on every
   valid tree within the deployed limits whose proof-of-work searches succeed has the tree's
   claims, is accepted by the deployed `verifyAggregate`, and is accepted by `V_I` with BLAKE2s run
   as the game runs it, within its budget `viCost N` (`N` at least the tree's size), unless a
   BLAKE2s compression collision exists. Not vacuous:
   an honest leanXMSS leaf (`SanityDeployed.sanity_deployed_xmssLeaf`).

Not yet here: completeness through recursion (the honest prover of a tree of aggregation nodes),
in progress; it will be added to this file.

## What is assumed

Nothing beyond the hypotheses of each theorem: leanXMSS's and leanSPHINCS's security, the signers'
and verifications' costs, the certificates of leanSPHINCS's parameter sets and V_I's per-node cost
are theorems (`lean_xmss`, `lean_sphincs`, `Reduction/*Bound.lean`, `BudgetCount.lean`), all at
Lean's three axioms.

What relates these theorems to the deployed system is not proved. It is the heuristic of
`e2e-security.md` §5:

* **The random-oracle heuristic**: BLAKE2s behaves as a random oracle natively; Fiat–Shamir holds
  for in-circuit-verified proofs; Flock's R1CS with the batched matrix claims behaves as
  oracle-consistent rows; in-circuit hash chains behave as visible queries. Caveats: CGH04,
  BBHMR19; static corruption only.
* **KA-pw (straight-line extraction of partial words)**: for every deployed adversary `A` there is
  an extractor `E_A` that reads, at every node `V_I` reaches, the partial word of `A`'s BLAKE2s
  trace under the node's stack root (the rows whose paths the trace answers, a hole at every
  maximal subtree whose digest the trace does not invert) and holes the present columns that
  disagree with a stack `q_ν` satisfying the leanISA relation on the node's input and agreeing with
  it on at least the Johnson threshold of present columns. Assumed: except with probability about
  `q_A · 2^-128`, whenever `verifyAggregate` accepts `A`'s output such a `q_ν` exists at every node
  `E_A` reaches. This is the deployed proof system's knowledge soundness with the BCS extractor at
  its own Johnson radius; T1 proves its random-oracle analogue (without Flock).
* With KA-pw, `sanity` turns `A` with `E_A` into an adversary of the game whose output `V_I`
  accepts with BLAKE2s, given also collision resistance of BLAKE2s compression (`StacksPrecheck`)
  and no cycle of nodes (`FuelBounds`); the random-oracle heuristic then carries `no_forgery` to
  the deployed `verifyAggregate`.

Proved without any heuristic, at the root only: `Guest.End.aggregate_sound_outer` (validity under
concrete BLAKE2s with a classical extractor; not a no-forgery statement).
-/

namespace LeanVM.E2E.Main

open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Rom OracleSpec OracleComp
open LeanVM.E2E
open scoped ENNReal

/-- **No forgery.** For every proved leanSPHINCS parameter set (`SphincsSet`), every numbers
`n_x`, `n_s` of honest keys, every tree size `N` and every adversary `A` making at most `qH` hash
queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests (`AdvBounds`, the only hypothesis):
`V_I`, on at most `N` nodes with the budget `viCost N`, accepts a root statement with a forged
claim of an honest key or an unbacked DA claim with probability at most

    q · noForgeryRate n_x n_s + 30 q²/2^256,

`q = totalQueries n_x n_s qH sX sS N` every hash evaluation of the game and
`noForgeryRate n_x n_s = (3 + 2 n_s + 1/16 + n_x/2^22)/2^128`: `λ₁ = 106` at `2^20 + 2^20` keys
(`aggregate_no_forgery_final_deployed`), `126` with leanXMSS keys only
(`aggregate_no_forgery_final_xmss`), `127 − k` whenever `n_s + 2 ≤ 2^k` (`noForgeryRate_le`). -/
theorem no_forgery [P : Sphincs.Params] [S : SphincsSet P] {nx ns : ℕ} (N : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      (totalQueries nx ns qH sX sS N : ℝ≥0∞) * noForgeryRate nx ns +
        ((30 * totalQueries nx ns qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  aggregate_no_forgery_final N A hA

/-- **No forgery with leanSPHINCS's sharp per-key bound.** As `no_forgery`, for the parameter sets
with their sharp multi-user bound (`SphincsSetSharp`, every proved set): at most

    q · noForgeryRateSharp n_x n_s + (30 + D n_s) q²/2^256,

`noForgeryRateSharp n_x n_s ≈ (4.81 + β n_s)/2^128` with `β ≈ 0.0020` at `full` and `0.0036` at
`pruned20`, and `D = SphincsSetSharp.quadD` (`2^13.41` at `full`), set by the certificates'
budget. -/
theorem no_forgery_sharp [P : Sphincs.Params] [S : SphincsSetSharp P] {nx ns : ℕ} (N : ℕ)
    (A : GameAdversary nx ns) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      (totalQueries nx ns qH sX sS N : ℝ≥0∞) * noForgeryRateSharp nx ns +
        (((30 + S.quadD * ns) * totalQueries nx ns qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  aggregate_no_forgery_final_sharp N A hA

/-- **No forgery at the deployed parameter sets**: `full` (subtree height 26) or `pruned20`,
`2^20` leanXMSS and `2^20` leanSPHINCS keys, every adversary: `q · 2^-116 + 2^34 q²/2^256`
(`λ₁ = 116.97` at `full`, `116.12` at `pruned20`). The hypothesis `hP` is
`sharp_full_deployed` or `sharp_pruned20_deployed`. -/
theorem no_forgery_sharp_deployed [P : Sphincs.Params] [S : SphincsSetSharp P]
    (hP : noForgeryRateSharp (2 ^ 20) (2 ^ 20) ≤ (2 : ℝ≥0∞)⁻¹ ^ 116 ∧
      30 + S.quadD * 2 ^ 20 ≤ 2 ^ 34)
    (N : ℕ) (A : GameAdversary (2 ^ 20) (2 ^ 20)) {qH sX sS : ℕ} (hA : AdvBounds A qH sX sS) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      (totalQueries (2 ^ 20) (2 ^ 20) qH sX sS N : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 116 +
        ((2 ^ 34 * totalQueries (2 ^ 20) (2 ^ 20) qH sX sS N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  aggregate_no_forgery_final_sharp_deployed hP N A hA

/-- **Completeness.** For every generator `gen` of valid honest trees within the deployed limits
(`ValidGen`: at most `N` nodes, the honest prover's queries at most `QP`) making at most `QG`
queries, a valid rate `ρ` and a proof-of-work fuel `pfuel ≤ 2^64`: the honest prover's idealized
proof, checked by `V_I` exactly as the game runs it (fuel `N`, budget `viCost N`, the same lazily
sampled oracle), is rejected with probability at most
`completeError (QG + QP) pfuel = Q((1 − 2^-17)^pfuel + Q/2^256) + Q(2^-192 + 4(Q + 1)/2^256)`,
`Q = QG + QP`. Not vacuous: `2^-124` at the honest leanXMSS leaf
(`Complete.idealVerify_complete_rom_xmssLeaf`). -/
theorem complete {nx ns : ℕ} {ρ pfuel N QG QP : ℕ} (hρ : LeanIsa.validRate ρ)
    (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option Complete.HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : Complete.ValidGen ρ pfuel N QP gen) :
    Pr{let z ← Complete.completeRunGame (nx := nx) (ns := ns) ρ pfuel gen N (viCost N)}[
      z.1 = some false] ≤ Complete.completeError (QG + QP) pfuel :=
  aggregate_complete_final hρ hpf gen hQG hgen

/-- **Sanity (T7″): `V_I` with BLAKE2s accepts what the deployed aggregation accepts.** If the
deployed outer verifier accepts the root statement `s` with the idealized proof's root proof
(`verifyAggregate`), every node `V_I` reaches has a partial word encoding one stack that satisfies
the leanISA relation on at least the Johnson threshold of present columns (`KnownStacks`, what
KA-pw provides), those stacks' tables have no BLAKE2s compression collision (`StacksPrecheck`), and
the fuel covers the reached nodes (`FuelBounds`), then `V_I` run with BLAKE2s accepts. -/
theorem sanity {s : Node.NodeStatement} {ip : IdealProof} {fuel : ℕ}
    (hagg : Node.verifyAggregate Guest.guest s ip.proof)
    (hkn : Sanity.KnownStacks Guest.guest ip (Sanity.rootNode Guest.guest s ip))
    (hpre : Sanity.StacksPrecheck Guest.guest ip (Sanity.rootNode Guest.guest s ip))
    (hfuel : Sanity.FuelBounds Guest.guest ip (Sanity.rootNode Guest.guest s ip) fuel) :
    idealVerify (m := Id) Sanity.blakeId Guest.guest ip fuel s = true :=
  Sanity.idealVerify_blake2s_known hagg hkn hpre hfuel

/-- **Sanity of the deployed system (S1).** For every honest witness tree `T` valid at BLAKE2s
(`T.Valid blake2sBytes`), within the deployed limits and budget at every node
(`WithinLimitsDep`), whose proof-of-work searches succeed within `pfuel` nonces (`PowFoundDep`),
at a valid rate `ρ`, and every `N` at least the tree's size: the deployed honest prover outputs a
root statement `s`, its proof `π` and an idealized proof `ip`; `s` makes exactly the tree's claims;
the deployed outer verifier accepts (`verifyAggregate`); `V_I`'s queries on it are within the
game's budget `viCost N`; and `V_I` run exactly as the game runs it (`budgetedQuery (viCost N)`,
fuel `N`, from the initial state, every hash query answered by BLAKE2s) accepts, unless two
non-final BLAKE2s compression rows with distinct inputs have equal outputs
(`CompressionCollision`). -/
theorem sanity_deployed {nx ns : ℕ} {b : Type → Type} [Monad b] [LawfulMonad b]
    (impl : QueryImpl GameSpec b)
    (himpl : ∀ x, simulateQ impl (liftM (HashSpec.query x) : OracleComp GameSpec Digest) =
      pure (Blake2sHash.blake2sBytes x))
    {ρ pfuel : ℕ} (T : Complete.HonestTree) (hρ : LeanIsa.validRate ρ)
    (hv : T.Valid Blake2sHash.blake2sBytes) (hlim : T.WithinLimitsDep ρ pfuel)
    (hpow : T.PowFoundDep ρ pfuel) {N : ℕ} (hN : T.size ≤ N) :
    ∃ s π ip, SanityDeployed.deployedProve ρ pfuel T = some (s, π, ip) ∧ s.claims = T.claims ∧
      Node.verifyAggregate Guest.guest s π ∧
      queryCount Blake2sHash.blake2sBytes Guest.guest ip N s ≤ viCost N ∧
      (simulateQ impl (((idealVerify (budgetedQuery (viCost N)) Guest.guest ip N s).run).run
          (SignState.init nx ns)) =
        pure (some true, { SignState.init nx ns with
          spent := queryCount Blake2sHash.blake2sBytes Guest.guest ip N s }) ∨
        SanityDeployed.CompressionCollision) :=
  SanityDeployed.sanity_deployed_budget_of_tree impl himpl ρ pfuel T hρ hv hlim hpow hN

end LeanVM.E2E.Main
