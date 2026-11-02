module

public import Statement.Theorems

/-!
# Corollaries

End statements that follow from `Statement.Theorems`, stated in their composed form: what an
accepted proof of the leanISA guest program establishes (`AggregateSound`), and the guest program's
completeness on the two simplest families of covered nodes (`GuestCompleteRecursion`,
`GuestCompleteLeaf`). `lean_vm` proves `LeanVM.corollaries_of_theorems`, that
`Statement.Theorems` implies `Statement.Corollaries` for the same extractor and decoder programs,
from the fields of `Theorems` alone, and `LeanVM.corollaries_hold`. A reviewer who trusts
`Theorems` need not read this file.
-/

@[expose] public section

open scoped ENNReal

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- **The decoding `decoding` explains the statement `statement`**: it is the deployed seed,
`statement` and a witness holding `statement`; or the decoded seed and statement, with the deployed
seed and `statement`, give a Keccak-256 collision among the candidates. -/
def ExplainsStatement (guest : LeanIsaProgram) (statement : NodeStatement)
    (decoding : SeedStatementAndWitness) : Prop :=
  (decoding.seed = deployedSeed guest ∧ decoding.statement = statement ∧
      NodeRelation (bytecodeWords guest) (deployedSeed guest) statement decoding.witness) ∨
    HasCollision
      (collisionCandidates decoding.seed decoding.statement (deployedSeed guest) statement)

open OracleComp OracleSpec in
/-- **The outer verifier's acceptance, explained.** In the random-permutation experiment of
`LeanVm.lean`, the adversary, querying `π` and `π⁻¹`, outputs a proof. The event: the verifier
accepts it as a proof of `guest` on the digest, under the deployed seed, of a statement `statement`
whose deferred claim has the guest program's shape, and yet the execution the knowledge extractor
`extractor` reads off the adversary's transcript and the proof does not explain `statement`: no
execution is extracted, or the decoder program `guestWitnessDecoder`, run on it within its budget
(`encodeGuestWitnessDecoderInput`, `guestWitnessDecoderBudget`, `Theorems.lean`), outputs the
encoding of no decoding that explains `statement` (`ExplainsStatement`: the deployed seed,
`statement` and a witness holding it, or a Keccak-256 collision among `collisionCandidates`). It
composes `KnowledgeSoundness`, `GuestKnowledgeSoundness` and `StatementDigestBinds`; its probability
is at most the bound of `KnowledgeSoundness`, `(Q + 2^14) · 2^-128 + 5 (Q + 2^14)² · 2^-256`, for
`Q ≤ 2^128` queries to `π`, `π⁻¹`. Keccak-256 and Keccak-f[1600] outside the executed program are
built from `π`; the statement's digest and the collisions are of the deployed Keccak-256, which the
guest program computes. -/
def AggregateSound (guest : LeanIsaProgram) (guestWitnessDecoder : LeanVM.Cost.MachineProgram)
    (extractor : StraightLineExtractor) : Prop :=
  ∀ (adversary : RandomPermutationAdversary) (Q : ℕ),
    Common.QueryCostAtMost adversary Common.permutationCallCost Q → Q ≤ 2 ^ 128 →
    Pr{let outcome ← knowledgeSoundnessExperiment adversary}[∃ statement : NodeStatement,
      outcome.accepted ∧ outcome.program = guest ∧
      publicInputDigest outcome.input = statementDigest (deployedSeed guest) statement ∧
      statement.deferredClaim.HasBytecodeShape (bytecodeWords guest) ∧
      ¬ ∃ execution, ∃ decoding : SeedStatementAndWitness,
        extractor outcome.program outcome.input outcome.transcript outcome.proof = some execution ∧
        Cost.outputWithin guestWitnessDecoder guestWitnessDecoderSizeBound
          (guestWitnessDecoderBudget execution)
          (Cost.encodeGuestWitnessDecoderInput outcome.program execution) =
            some (Cost.encodeValue decoding) ∧
        ExplainsStatement guest statement decoding] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM.Node

namespace LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest LeanVM.Guest.Coverage

/-- **Every recursion node of at most `2048` claims has a valid execution of the leanISA guest
program**: for every statement `statement` and witness `witness` with `NodeRelation` under the
deployed seed, within the deployed limits (so at most `16` children), every child carrying an honest
proof (`HonestChild`), holding no raw leanXMSS or leanSPHINCS signature and no blob directly, with
at most `2048` declared claims, coverage slots and children's declared claims, there is a valid
execution of the leanISA guest program on the statement's digest of committed size in
`[2^22, 2^28]`. The first family of `CoveredNode`. -/
abbrev GuestCompleteRecursion : Prop :=
  ∀ (statement : NodeStatement) (witness : NodeWitness),
    NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness →
    DeployedLimits statement witness → (∀ child ∈ witness.children, HonestChild child) →
    (heldDirectly statement.claims.xmss witness.xmssHolders).length = 0 →
      (heldDirectly statement.claims.sphincs witness.sphincsHolders).length = 0 →
    witness.daMatrix = none →
    statement.claims.xmss.length + statement.claims.sphincs.length ≤ 2048 →
    coverageSlots statement witness ≤ 2048 →
    (witness.children.map fun child ↦ child.statement.claims.xmss.length +
      child.statement.claims.sphincs.length).sum ≤ 2048 →
    ∃ execution : Execution guestProgram,
      ValidExecution guestProgram
        (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) execution ∧
      2 ^ 22 ≤ execution.committedSize ∧ execution.committedSize ≤ 2 ^ 28

/-- **Every leaf of at most `2048` raw signatures has a valid execution of the leanISA guest
program**: for every statement `statement` and witness `witness` with `NodeRelation` under the
deployed seed, within the deployed limits, with no child and no blob held directly, at most `2048`
raw leanXMSS and leanSPHINCS signatures together and at most `2048` declared claims and coverage
slots, there is a valid execution of the leanISA guest program on the statement's digest of
committed size in `[2^22, 2^28]`. The second family of `CoveredNode`. -/
abbrev GuestCompleteLeaf : Prop :=
  ∀ (statement : NodeStatement) (witness : NodeWitness),
    NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness →
    DeployedLimits statement witness → witness.children = [] → witness.daMatrix = none →
    (heldDirectly statement.claims.xmss witness.xmssHolders).length +
      (heldDirectly statement.claims.sphincs witness.sphincsHolders).length ≤ 2048 →
    statement.claims.xmss.length + statement.claims.sphincs.length ≤ 2048 →
    coverageSlots statement witness ≤ 2048 →
    ∃ execution : Execution guestProgram,
      ValidExecution guestProgram
        (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) execution ∧
      2 ^ 22 ≤ execution.committedSize ∧ execution.committedSize ≤ 2 ^ 28

end LeanVM.Guest.Completeness

namespace Statement

/-- **The corollaries**, each following from `Theorems`, for the same extractor and decoder
programs (two parameters of the same type: every use names them). -/
structure Corollaries
    (leanVmKnowledgeExtractor guestWitnessDecoder : LeanVM.Cost.MachineProgram) : Prop where
  /-- An accepted proof of the leanISA guest program on the digest of `s` under the deployed seed is
  explained by the execution the extractor program extracts (the decoder program outputs, on it, the
  encoding of that seed, `s` and a witness holding `s`) or by a Keccak-256 collision, except with
  the bound of `leanVmKnowledgeSoundness`: from `leanVmKnowledgeSoundness`,
  `guestKnowledgeSoundness` and `statementDigestBinds`. -/
  aggregateSound : LeanVM.Node.AggregateSound LeanVM.Guest.guestProgram guestWitnessDecoder
    (LeanVM.extractorComputedBy leanVmKnowledgeExtractor)
  /-- The leanISA guest program is complete on every recursion node of at most `2048` claims
  holding no raw signature and no blob itself, its children carrying honest proofs: from
  `guestCompleteOnHonestChildren`. -/
  guestCompleteRecursion : LeanVM.Guest.Completeness.GuestCompleteRecursion
  /-- The leanISA guest program is complete on every leaf of at most `2048` raw signatures, holding
  no blob: from `guestCompleteOnHonestChildren`. -/
  guestCompleteLeaf : LeanVM.Guest.Completeness.GuestCompleteLeaf

end Statement

end
