import LeanVM.E2E.KS.Unforgeable
import LeanVM.E2E.Sanity
import LeanVM.E2E.SanityDeployed
import LeanVM.E2E.SanityDeployedBudget
import LeanVM.E2E.Complete.Rom.PadRec

/-!
# The end-to-end security of leanVM aggregation: the result

leanVM aggregates leanXMSS and leanSPHINCS signatures into one succinct proof, checked by the
deployed verifier `verifyAggregate`. This file states what is proved about it; every other theorem
under `LeanVM/E2E/` is a step of their proofs. The design is `docs/roadmap/e2e-security.md` (§7
the decisions; the form, E2E-15).

| Property | Theorem | Statement |
|---|---|---|
| **Unforgeable** | `unforgeable` | `KnowledgeSound ε` ⇒ `Pr ≤ ε + (n_s + n_x/2^23 + 4) q / 2^127` |
| **Correct** | `correct` | the honest aggregate of a valid tree is accepted by `verifyAggregate` |

`n_x`, `n_s` are the numbers of honest leanXMSS and leanSPHINCS keys, `q` the hash evaluations of
the game. At `2^20 + 2^20` keys, `ε + q / 2^106` (`unforgeable_deployed`). No cap on `q`.

## The model (`LeanVM/E2E/KS/Game.lean`)

* **The oracle.** One random oracle `H : Bytes → Digest` (BLAKE2s idealized), lazily sampled and
  shared by every party: the adversary, the honest signers and the verifier.
* **The verifier.** The deployed `verifyAggregate`, run with `H` (`verifyAggregateWith`; at BLAKE2s
  it is `verifyAggregate`, `verifyAggregateWith_blake2s`).
* **The game** (`dGame`): `n_x` leanXMSS and `n_s` leanSPHINCS honest keys from uniform seeds; the
  adversary `A` receives their public keys, queries `H` and the honest signers (a leanXMSS key
  refuses a reused leaf, a leanSPHINCS key its `signatureLimit`), and outputs a root statement
  `s` and a proof `π`; the verifier checks them. `A`'s hash queries and answers are recorded, in
  order: its transcript.
* **The event** (`DForged`): the verifier accepts and `s` holds a claim `(pk_j, m)` of an honest
  key on a message no request to that key was answered for.
* **The resource** (`DHashEvals A q`): the game makes at most `q` hash evaluations before
  verification: the key generations, `A`'s hash queries, and the signatures it requests at their
  proved worst-case costs.

## The assumption: knowledge soundness

`KnowledgeSound guest A ε` (a hypothesis of `unforgeable`, not proved): except with probability
`ε`, whenever the verifier accepts `A`'s output, every signature claim `(pk, m)` of `s` has a
signature valid under the answers of `A`'s own hash queries. It is straight-line extraction (an
extractor reading `A`'s transcript, no rewinding), so `ε` does not grow with the recursion's depth;
it is the deployed proof system's knowledge soundness (WHIR, Fiat–Shamir, the recursion verifying
children in-circuit), expected about `q · 2^-128` (§5). Everything else is proved: leanXMSS's and
leanSPHINCS's multi-user security, the signers' costs and the composition.

## Supporting results: the idealized model

Why the assumption is plausible: in the random-oracle model, the recursion's soundness is proved
for an idealized, non-succinct verifier `V_I` (`idealVerify`, `LeanVM/E2E/Statement.lean`), given
the data behind every node's commitment (an idealized proof):

* `ideal_unforgeable`: `V_I` accepts a forged claim or an unbacked DA claim with probability at
  most `(n_s + n_x/2^23 + 4) · q / 2^127`, `q` the game's hash evaluations, `V_I`'s budget
  included (`HashEvals`); the knowledge it needs is proved there, at every depth (T1–T5).
* `ideal_correct`: the honest prover's idealized proof of a tree of any depth is rejected by `V_I`
  with probability at most `completeError`.
* `ideal_faithful` (S1): the deployed honest aggregation is accepted by `V_I` with BLAKE2s too.
* `sanity` (T7″): `V_I` with BLAKE2s accepts what `verifyAggregate` accepts when the reached
  nodes' committed data decode to known executions (what KA-pw, `e2e-security.md` §5, provides).

Proved and pinned, not restated here: the sharp leanSPHINCS bound of the idealized model
(`aggregate_unforgeable_sharp_deployed`, `q / 2^116 + 2^34 q²/2^256`), its leanXMSS-only form
(`q / 2^124`), and the generator-level completeness (`aggregate_complete_final`).
-/

namespace LeanVM.E2E.Main

open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Rom OracleSpec OracleComp
open LeanVM.E2E LeanVM.E2E.KS
open scoped ENNReal

/-! ## Unforgeable -/

/-- **Unforgeable.** For every proved leanSPHINCS parameter set (`SphincsSet`), every numbers
`n_x`, `n_s` of honest keys and every adversary `A` whose game makes at most `q` hash evaluations
before verification (`DHashEvals`): if the deployed aggregation is knowledge sound against `A` with
error `ε` (`KnowledgeSound`, the assumption), the deployed verifier `verifyAggregate`, run with the
random oracle, accepts a root statement with a forged claim of an honest key with probability at
most

    ε + (n_s + n_x/2^23 + 4) · q / 2^127,

for every `q`: about `log₂ n_s` bits below `127`, the leanXMSS keys almost free. -/
theorem unforgeable [P : Sphincs.Params] [S : SphincsSet P] {nx ns q : ℕ} {ε : ℝ≥0∞}
    (A : DAdversary nx ns) (hq : DHashEvals A q) (hks : KnowledgeSound Guest.guest A ε) :
    Pr{let z ← dGame Guest.guest A}[z.1.accepted = true ∧ DForged z.1] ≤
      ε + ((ns : ℝ≥0∞) + nx / 2 ^ 23 + 4) * q / 2 ^ 127 :=
  aggregate_unforgeable_ks Guest.guest A hq hks

/-- **Unforgeable at `2^20 + 2^20` keys: `ε + q / 2^106`**, every parameter set. -/
theorem unforgeable_deployed [P : Sphincs.Params] [S : SphincsSet P] {q : ℕ} {ε : ℝ≥0∞}
    (A : DAdversary (2 ^ 20) (2 ^ 20)) (hq : DHashEvals A q)
    (hks : KnowledgeSound Guest.guest A ε) :
    Pr{let z ← dGame Guest.guest A}[z.1.accepted = true ∧ DForged z.1] ≤ ε + q / 2 ^ 106 :=
  aggregate_unforgeable_ks_deployed Guest.guest A hq hks

/-- **The game's verifier is the deployed one**: `verifyAggregateWith` at BLAKE2s is
`verifyAggregate`. -/
theorem verifier_eq (s : Node.NodeStatement) (π : Proof) :
    Id.run (verifyAggregateWith (m := Id) Blake2sHash.blake2sBytes Guest.guest s π) = true ↔
      Node.verifyAggregate Guest.guest s π :=
  verifyAggregateWith_blake2s Guest.guest s π

/-! ## Correct -/

/-- **Correct.** For every honest witness tree `T` (aggregation nodes over aggregation nodes over
signatures, any depth) valid at BLAKE2s (`T.Valid blake2sBytes`), within the deployed limits and
budget at every node (`WithinLimitsDep`), whose proof-of-work searches succeed within `pfuel`
nonces (`PowFoundDep`), at a valid rate `ρ`: the deployed honest prover outputs a root statement
`s` and a proof `π` (and the idealized proof `ip` of the supporting results); `s` makes exactly
the tree's claims, and the deployed verifier accepts: `verifyAggregate guest s π`. -/
theorem correct {ρ pfuel : ℕ} (T : Complete.HonestTree) (hρ : LeanIsa.validRate ρ)
    (hv : T.Valid Blake2sHash.blake2sBytes) (hlim : T.WithinLimitsDep ρ pfuel)
    (hpow : T.PowFoundDep ρ pfuel) :
    ∃ s π ip, SanityDeployed.deployedProve ρ pfuel T = some (s, π, ip) ∧ s.claims = T.claims ∧
      Node.verifyAggregate Guest.guest s π := by
  obtain ⟨s, π, ip, h, hc, hv', -⟩ :=
    SanityDeployed.sanity_deployed_of_tree ρ pfuel T hρ hv hlim hpow le_rfl
  exact ⟨s, π, ip, h, hc, hv'⟩

/-! ## Supporting results: the idealized model -/

/-- **Unforgeable, idealized model.** For every proved leanSPHINCS parameter set (`SphincsSet`),
every numbers `n_x`, `n_s` of honest keys, every tree size `N` and every adversary `A` whose game
makes at most `q` hash evaluations (`HashEvals`, the only hypothesis): `V_I`, on at most `N` nodes
with the budget `viCost N`, accepts a root statement with a forged claim of an honest key or an
unbacked DA claim with probability at most

    (n_s + n_x/2^23 + 4) · q / 2^127,

for every `q`: about `log₂ n_s` bits below `127`, the leanXMSS keys almost free. -/
theorem ideal_unforgeable [P : Sphincs.Params] [S : SphincsSet P] {nx ns N q : ℕ}
    (A : GameAdversary nx ns) (hq : HashEvals A N q) :
    Pr{let z ← game Guest.guest N (viCost N) A}[Breaks z.1 z.2] ≤
      ((ns : ℝ≥0∞) + nx / 2 ^ 23 + 4) * q / 2 ^ 127 :=
  aggregate_unforgeable A hq

/-- **Correct, idealized model.** For every generator `gen` of valid honest trees of any depth
(aggregation nodes over aggregation nodes over signatures), within the deployed limits and budget on
their claims and holders at every node (`ValidGenR`: `LimitsT`, which names no hash and no prover;
at most `N` nodes; the honest prover's queries at most `QP`) making at most `QG` queries, a valid
rate `ρ` and a proof-of-work fuel `pfuel ≤ 2^64`: the honest prover's idealized proof, checked by
`V_I` exactly as the game runs it (fuel `N`, budget `viCost N`, the same lazily sampled oracle), is
rejected with probability at most `completeError (QG + QP) pfuel = Q((1 − 2^-17)^pfuel + Q/2^256) +
Q(2^-192 + 4(Q + 1)/2^256)`, `Q = QG + QP`. The honest prover pads each node's memory, as leanVM's
prover does, so that every child's stack has the 22 variables its parent's guest admits
(`Complete.guestCompleteModel_big`). Not vacuous: `2^-124` at the honest leanXMSS leaf and at a root
over it (`Complete.idealVerify_complete_rom_xmssLeaf`,
`Complete.idealVerify_complete_rom_xmssRoot`). -/
theorem ideal_correct {nx ns : ℕ} {ρ pfuel N QG QP : ℕ} (hρ : LeanIsa.validRate ρ)
    (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option Complete.HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : Complete.ValidGenR ρ pfuel N QP gen) :
    Pr{let z ← Complete.completeRunGame (nx := nx) (ns := ns) ρ pfuel gen N (viCost N)}[
      z.1 = some false] ≤ Complete.completeError (QG + QP) pfuel :=
  aggregate_complete_final hρ hpf gen hQG (Complete.validGen_of_R hρ hgen)

/-- **Faithful, idealized model (S1): the deployed honest aggregation is accepted by both
verifiers.** For every
honest witness tree `T` valid at BLAKE2s (`T.Valid blake2sBytes`), within the deployed limits and
budget at every node (`WithinLimitsDep`), whose proof-of-work searches succeed within `pfuel` nonces
(`PowFoundDep`), at a valid rate `ρ`, and every `N` at least the tree's size: the deployed honest
prover outputs a root statement `s`, its proof `π` and an idealized proof `ip`; `s` makes exactly
the tree's claims; the deployed outer verifier accepts (`verifyAggregate`); `V_I`'s queries on it
are within the game's budget `viCost N`; and `V_I` run exactly as the game runs it
(`budgetedQuery (viCost N)`, fuel `N`, from the initial state, every hash query answered by
BLAKE2s) accepts, unless two non-final BLAKE2s compression rows with distinct inputs have equal
outputs (`CompressionCollision`). -/
theorem ideal_faithful {nx ns : ℕ} {b : Type → Type} [Monad b] [LawfulMonad b]
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

end LeanVM.E2E.Main
