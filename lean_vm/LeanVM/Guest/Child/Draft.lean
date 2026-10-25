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

/-- **The nodes the deployed budget covers**, by their work: a recursion node of at most `2048`
claims (at most `16` children by `Limits`), a leaf of at most `2048` raw signatures (the two
statements above), a recursion node of at most `8` children and `2^15` claims, a node of at most
`4` children and `1024` raw signatures with at most `8192` claims, a node of at most `4`
children checking a blob of at most `8` rows with at most `2048` claims, and a node of at most `2`
children, `256` raw signatures and a blob of at most `4` rows with at most `4096` claims ("claims":
the declared claims, the coverage slots and the children's claims; "raw signatures": leanXMSS and
leanSPHINCS together; a node holds at most one blob directly, by `Limits`). -/
def Covered (u : End.Work) : Prop :=
  (u.rawXmss + u.rawSphincs = 0 ∧ u.rawDa = 0 ∧
    u.declared ≤ 2048 ∧ u.coverage ≤ 2048 ∧ u.childClaims ≤ 2048) ∨
  (u.children = 0 ∧ u.rawDa = 0 ∧ u.rawXmss + u.rawSphincs ≤ 2048 ∧
    u.declared ≤ 2048 ∧ u.coverage ≤ 2048) ∨
  (u.children ≤ 8 ∧ u.rawXmss + u.rawSphincs = 0 ∧ u.rawDa = 0 ∧
    u.declared ≤ 2 ^ 15 ∧ u.coverage ≤ 2 ^ 15 ∧ u.childClaims ≤ 2 ^ 15) ∨
  (u.children ≤ 4 ∧ u.rawXmss + u.rawSphincs ≤ 1024 ∧ u.rawDa = 0 ∧
    u.declared ≤ 8192 ∧ u.coverage ≤ 8192 ∧ u.childClaims ≤ 8192) ∨
  (u.children ≤ 4 ∧ u.rawXmss + u.rawSphincs = 0 ∧ u.rawDaRows ≤ 8 ∧
    u.declared ≤ 2048 ∧ u.coverage ≤ 2048 ∧ u.childClaims ≤ 2048) ∨
  (u.children ≤ 2 ∧ u.rawXmss + u.rawSphincs ≤ 256 ∧ u.rawDaRows ≤ 4 ∧
    u.declared ≤ 4096 ∧ u.coverage ≤ 4096 ∧ u.childClaims ≤ 4096)

/-- **Every covered node has a valid execution of the guest**: for every seed, statement `s` and
witness `w` with `NodeRel`, within the deployed limits, the caps agreeing and no zero challenge
where the guest divides, whose work is covered (`Covered`: recursion nodes, leaves, mixed nodes
and nodes checking a blob, within the sizes it lists), there is a valid execution of the guest on
the statement's digest of committed size in `[2^22, 2^28]`. Proved by
`LeanVM.Guest.Budget.guest_complete_covered`. -/
abbrev GuestCompleteCovered : Prop :=
  ∀ (seed : Digest) (s : NodeStatement) (w : NodeWitness),
    NodeRel bytecode seed s w → Limits bytecode s w →
    CapsAgree bytecode seed w → NoZeroChallenge bytecode seed w → Covered (work s w) →
    ∃ t : Trace guest, ValidExecution guest (publicInputOf (statementDigest seed s)) t ∧
      2 ^ 22 ≤ t.committedSize ∧ t.committedSize ≤ 2 ^ 28

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
2. its proof with the deployed Keccak (`atKeccak`) of an execution of the guest on a statement's
   digest under the deployed seed, of committed size at least `2^22` (as the executions of
   `GuestCompleteRecursion`, `GuestCompleteLeaf` and `GuestCompleteCovered` are), whenever
   `verifierNZ` with the deployed Keccak accepts it, is with the statement (its deferred claim
   shaped) and some claims on the bytecode a child the guest accepts under the deployed seed
   (`ChildOk`).
Proved by `LeanVM.Guest.Budget.guest_child_complete`. -/
def GuestChildComplete : Prop :=
  ∃ prover : HonestProver,
    (∀ (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ),
      ValidExecution prog input t → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
      Pr{let v ← (simulateQ LeanVM.rpmImpl (do
          let proof ← prover prog input t ρ (2 ^ 25)
          verifierNZ queryH queryF prog input proof)).run' []}[v = false] ≤
        (2 : ℝ≥0∞)⁻¹ ^ 126) ∧
    ∀ (s : NodeStatement) (t : Trace guest) (ρ : ℕ), 2 ^ 22 ≤ t.committedSize →
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
