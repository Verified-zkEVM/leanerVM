/-
  LeanVM.Guest.Child.Draft

  The draft of the completeness section's additions to `Statement/LeanVmGuest.lean` (moved there
  once proved): honest proofs are children the guest accepts.
-/

module

public import Statement.LeanVmGuest

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (work bytecode publicInputOf)

@[expose] public section

open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier OracleComp OracleSpec
open scoped ENNReal

/-- **The leanVM verifier refusing a zero challenge where the guest divides**, with the hash `H`
and the permutation `F` in any monad: `verifier H F` whose stacked opening also refuses a zero
fold, tail or level batching challenge (`Limits.verifyExecutionNZ`). -/
def verifierNZ {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KState → m KState)
    (prog : Program) (input : PublicInput) (proof : Proof) : m Bool := do
  let seed ← seedWith H F (bytecodeWords prog) (publicDigest input)
  runProof H F (do
    Limits.verifyExecutionNZ .computed (bytecodeWords prog) (publicDigest input)
    return true) seed proof

/-- Keccak-256 and Keccak-f[1600] answering the verifier's and the honest prover's calls
(`HashSpec`). -/
def keccakImpl : QueryImpl HashSpec Id
  | .inl x => keccak256 x
  | .inr s => keccakF s

/-- **An honest prover's proof with the deployed Keccak-256 and Keccak-f[1600].** -/
def atKeccak (prover : HonestProver) (prog : Program) (input : PublicInput)
    (t : Trace prog) (ρ fuel : ℕ) : Proof :=
  Id.run (simulateQ keccakImpl (prover prog input t ρ fuel))

/-- **A child the guest accepts** under the seed `seed`: what `GuestCompleteRecursion` assumes of
each child (its statement's deferred claim shaped and its proof accepted by the deferring verifier,
`NodeRel`; its announced stack log at least `22` and its stream at most `8192` scalars, `Limits`;
its openings agreeing in the caps, `CapsAgree`; no zero challenge where the guest divides,
`NoZeroChallenge`). -/
structure ChildOk (bytecode : List K) (seed : Digest) (c : Child) : Prop where
  shaped : c.statement.defer.Shaped bytecode
  verifies : verifyDeferred bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true
  stackLog : ∀ layout r, announced bytecode c.proof.stream = some (layout, r) →
    Hints.muMin ≤ layout.stackLog
  stream : c.proof.stream.length ≤ Hints.streamCap
  capsAgree : ∀ b ∈ Limits.queriesOf
      (deferredProgram c.fresh bytecode (statementDigest seed c.statement)) (Hints.childStart seed c),
    Limits.BatchAgrees b.1 b.2
  noZeroChallenge :
    Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true

/-- **The honest proof of a guest execution is a child the guest accepts**: there is an honest
prover such that
1. in the random-permutation model, trying `2^25` nonces per proof of work, the verifier refusing a
   zero challenge where the guest divides (`verifierNZ`) rejects its proof of a valid execution
   within the verifier's size cap, at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4`, with probability at
   most `2^-126` (`LeanVM.Completeness`'s experiment with `verifierNZ` for the verifier);
2. its proof with the deployed Keccak (`atKeccak`) of a valid execution of the guest
   on a statement's digest under the deployed seed, of committed size in `[2^22, 2^28]` (those of
   `GuestCompleteRecursion` and `GuestCompleteLeaf`), at such a rate, whenever `verifierNZ` with the
   deployed Keccak accepts it, is with the statement (its deferred claim shaped) and some claims on
   the bytecode a child the guest accepts under the deployed seed (`ChildOk`).
Proved by `LeanVM.Guest.Budget.guest_child_complete`. -/
def GuestChildComplete : Prop :=
  ∃ prover : HonestProver,
    (∀ (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ),
      ValidExecution prog input t → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
      Pr{let v ← (simulateQ LeanVM.rpmImpl (do
          let proof ← prover prog input t ρ (2 ^ 25)
          verifierNZ queryH queryF prog input proof)).run' []}[v = false] ≤
        (2 : ℝ≥0∞)⁻¹ ^ 126) ∧
    ∀ (s : NodeStatement) (t : Trace guest) (ρ : ℕ),
      ValidExecution guest (publicInputOf (statementDigest (deployedSeed guest) s)) t →
      2 ^ 22 ≤ t.committedSize → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
      s.defer.Shaped bytecode →
      verifierNZ (m := Id) keccak256 keccakF guest
          (publicInputOf (statementDigest (deployedSeed guest) s))
          (atKeccak prover guest (publicInputOf (statementDigest (deployedSeed guest) s)) t ρ
            (2 ^ 25)) = true →
      ∃ fresh, ChildOk bytecode (deployedSeed guest) ⟨s, fresh,
        atKeccak prover guest (publicInputOf (statementDigest (deployedSeed guest) s)) t ρ
          (2 ^ 25)⟩

end
end LeanVM.Guest.Budget
