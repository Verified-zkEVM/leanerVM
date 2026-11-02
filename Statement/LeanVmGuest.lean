module

public import Statement.LeanVmGuestDigest
public import Statement.LeanDa
public import Statement.Data.Bytecode
public import Statement.Fast.Schemes

/-!
# The leanISA guest program: what a node proves

A node of the aggregation has claims (`NodeStatement`: leanXMSS and leanSPHINCS claims, a DA
digest, and a claim on the guest program's bytecode it defers) and witnesses (`NodeWitness`: raw
signatures, a blob matrix, children carrying proofs, the batching's hints). What a valid execution
of the guest program establishes is that the witnesses cover the claims, `NodeRelation`:

* `ClaimsCovered`: every leanXMSS and leanSPHINCS claim is held by a raw signature that verifies,
  or by a child whose statement lists it;
* `DaClaimCovered`: the DA digest is that of the blob matrix the node checks, zeros, or a child's;
* `ChildrenProven`: every child's proof is accepted, for the child's statement, by the deferring
  verifier, which takes the bytecode's value at the child's point from the witness;
* `DeferredClaimBatched`: the node's claim on the bytecode batches its children's (that value is
  checked only at the root, in the batched claim);

and the node's own claim on the bytecode has the bytecode's shape.

The node's public input is its statement's digest under a seed (`statementDigest`). After the
relation: what a decoding of an execution explains (`ExplainsPublicInput`, of which
`GuestKnowledge`, `Theorems.lean`, is the end statement) and the binding of the statement's digest
(`StatementDigestBinds`). The statement's types, its digest and the batching program
(`Batch.nodeBatchingProgram`), reference material, are `LeanVmGuestDigest.lean`'s, which Lean needs
first; the completeness side is `LeanVmGuestCompleteness.lean`.

Transcribed from leanVM at the pin (`../leanvm-rev`): `crates/rec_aggregation/src/aggregation.rs`
(the statement, its digest, the batching) and `crates/rec_aggregation/guests/lean_ethereum.py`
(the guest program); `aggregation.rs:N` and `lean_ethereum.py:N` are lines of those files at the
pin. The signature schemes are `LeanXmss.lean`'s and `LeanSphincs.lean`'s with Keccak-256 as their
hash; LeanDA is `LeanDa.lean`'s.

The witness is the knowledge content: "some signature verifies" says little (some signature
verifies for almost every key and message). The soundness statement takes the decoder that names
the witness as a parameter, a program of the cost machine run within a budget (`GuestKnowledge`).
A program that output another statement of the same digest would exhibit a Keccak-256 collision;
what excludes it is that none is known. That the root's statement makes every claim held at the
leaves is not proved: it would need the Keccak computed inside the guest program to behave as the
random permutation of `LeanVM.KnowledgeSoundness`.
-/

@[expose] public section

/-! ## The witnesses -/

namespace LeanVM.Da

open LeanVM.Parameters

/-- What holds a DA claim: a matrix of codewords and the vector its rows are orthogonal to. -/
structure MatrixWitness where
  /-- The codewords, one per row. -/
  rows : List (List K)
  /-- The vector every row is orthogonal to. -/
  orthogonalVector : List E

end LeanVM.Da

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- A child of a node: its statement, its proof, and what the proof claims of the bytecode. -/
structure Child where
  /-- The child's node statement. -/
  statement : NodeStatement
  /-- The claim on the bytecode its proof makes. -/
  freshClaim : BytecodeClaim
  /-- Its proof. -/
  proof : Proof

/-- How a node holds a claim: directly, by a witness, or through its `childIndex`-th child. -/
inductive ClaimHolder (Witness : Type) where
  /-- Directly, by the witness. -/
  | direct (witness : Witness)
  /-- Through a child. -/
  | child (childIndex : ℕ)

/-- What a node holds its statement by: its children, a holder for every signature claim, the blob
matrix it checks directly with the DA claim it opens (if any), and the batching's hints. -/
structure NodeWitness where
  /-- The children. -/
  children : List Child
  /-- A holder for each leanXMSS claim, in order. -/
  xmssHolders : List (ClaimHolder LeanXmss.Signature)
  /-- A holder for each leanSPHINCS claim, in order. -/
  sphincsHolders : List (ClaimHolder Sphincs.Signature)
  /-- The blob matrix the node checks directly, with the DA claim it opens. -/
  daMatrix : Option (DaClaim × Da.MatrixWitness)
  /-- The prover's part of the batching of the children's deferred claims. -/
  batchingHints : BatchingHints

/-- The deferred claim has the shape of the bytecode `bytecode`: a point of `log₂` of its length
(`bytecode_vars`, `aggregation.rs:795-797`; `BYTECODE_VARS`, `lean_ethereum.py:325`). -/
def DeferredClaim.HasBytecodeShape (bytecode : List K) (claim : DeferredClaim) : Prop :=
  claim.bytecodePoint.length = Nat.log2 bytecode.length

/-- What a leaf defers: the bytecode at the all-zero point (`DeferredClaim::leaf`,
`aggregation.rs:250-252`; `main`'s leaf branch, `lean_ethereum.py:4210-4218`). The value is the
outer verifier's to check. -/
def DeferredClaim.HasZeroPoint (bytecode : List K) (claim : DeferredClaim) : Prop :=
  claim.bytecodePoint = List.replicate (Nat.log2 bytecode.length) 0

/-! ## What the guest program proves

`NodeRelation` first, then each of its conditions with what it reads. (A `mutual` block only so
that the relation reads before its parts: nothing in it is recursive.) -/

mutual

/-- **What the witness `witness` establishes of the statement `statement`**, for the guest
program's bytecode `bytecode` and under the seed `seed`: the witnesses cover the claims (the four
conditions below), and the statement's deferred claim has the bytecode's shape. -/
def NodeRelation (bytecode : List K) (seed : Digest) (statement : NodeStatement)
    (witness : NodeWitness) : Prop :=
  ClaimsCovered statement witness ∧ DaClaimCovered statement witness ∧
    ChildrenProven bytecode seed witness ∧ DeferredClaimBatched bytecode seed statement witness ∧
    statement.deferredClaim.HasBytecodeShape bytecode

/-- **Every signature claim is covered**: the `i`-th leanXMSS claim by the `i`-th leanXMSS
holder, a raw signature that verifies at any leaf index or a child whose statement lists the
claim; likewise for leanSPHINCS. Two equal claims may share a holder. -/
def ClaimsCovered (statement : NodeStatement) (witness : NodeWitness) : Prop :=
  List.Forall₂ (ClaimIsHeld (fun (claim : LeanXmssClaim) signature ↦
      leanXmssVerifyWithKeccak claim.1 claim.2 signature = true) NodeClaims.xmss witness.children)
    statement.claims.xmss witness.xmssHolders ∧
  List.Forall₂ (ClaimIsHeld (fun (claim : LeanSphincsClaim) signature ↦
      leanSphincsVerifyWithKeccak claim.1 claim.2 signature = true) NodeClaims.sphincs
      witness.children)
    statement.claims.sphincs witness.sphincsHolders

/-- **A claim is held** by a holder: a witness that `holds` it, or a child whose claims of the
kind (`claimsOf`) list it. -/
def ClaimIsHeld {Claim Witness : Type} (holds : Claim → Witness → Prop)
    (claimsOf : NodeClaims → List Claim) (children : List Child) (claim : Claim) :
    ClaimHolder Witness → Prop
  | .direct witness => holds claim witness
  | .child childIndex =>
    ∃ child, children[childIndex]? = some child ∧ claim ∈ claimsOf child.statement.claims

/-- leanXMSS verification over Keccak-f[1600], the hash Keccak-256. The leaf index is the
signature's. -/
def leanXmssVerifyWithKeccak (publicKey : HashSig.PublicKey) (message : HashSig.Message)
    (signature : LeanXmss.Signature) : Bool :=
  Id.run (LeanXmss.Verification.verify (m := Id) keccakF1600 publicKey message signature)

/-- leanSPHINCS verification over Keccak-f[1600], the hash Keccak-256. -/
def leanSphincsVerifyWithKeccak (publicKey : Sphincs.PublicKey) (message : Sphincs.Message)
    (signature : Sphincs.Signature) : Bool :=
  Id.run (Sphincs.Verification.verify (m := Id) keccakF1600 publicKey message signature)

/-- **The DA digest is covered**: it is the digest of the DA claim that the matrix checked here
opens; without such a matrix, zero or some child's DA digest (`da_pick`,
`lean_ethereum.py:4202-4206`). -/
def DaClaimCovered (statement : NodeStatement) (witness : NodeWitness) : Prop :=
  match witness.daMatrix with
  | some (claim, matrix) =>
    statement.claims.daDigest = daClaimDigest claim ∧
      LeanVM.Da.MatrixWitness.Opens claim.daRoot claim.membershipVectorDigest matrix
  | none =>
    statement.claims.daDigest = zeroDigest ∨
      ∃ child ∈ witness.children, child.statement.claims.daDigest = statement.claims.daDigest

/-- **The matrix opens the DA claim `⟨root, vectorDigest⟩`** (`da_verify`,
`lean_ethereum.py:3915-4053`): `1` to `1024` codewords of `2^15` symbols commit to `root`, each is
orthogonal to the vector, and the vector's digest is `vectorDigest` (two-level,
`LeanDa.vectorDigest`, `da_vector_cell`, `lean_ethereum.py:4043-4053`), all over Keccak-f[1600]
with LeanDA's digests as 32 bytes. Only where the vector is the root's membership vector, as the
deployed outer verifier requires (no end statement here assumes it), are the rows codewords,
except with the membership test's error (`lean_da`'s `membershipVector_eq_dual`,
`checker_sound`) and up to a collision of the vector digest, not among `collisionCandidates`; the
link to `lean_da`'s code binding is not proved. The prover's copy of the membership vector
(`crates/lean_da/src/membership.rs`) is not transcribed. -/
def _root_.LeanVM.Da.MatrixWitness.Opens (root vectorDigest : Digest)
    (witness : LeanVM.Da.MatrixWitness) : Prop :=
  1 ≤ witness.rows.length ∧ witness.rows.length ≤ LeanDa.maxRows ∧
    (∀ row ∈ witness.rows, row.length = 2 ^ LeanDa.logM) ∧
    LeanDa.commitCodewords keccakF1600 witness.rows = root.toBytes ∧
    witness.orthogonalVector.length = 2 ^ LeanDa.logM ∧
    LeanDa.vectorDigest keccakF1600 witness.orthogonalVector = vectorDigest.toBytes ∧
    ∀ row ∈ witness.rows, LeanDa.innerProduct (fun b ↦ witness.orthogonalVector.getD b 0)
      (fun b ↦ row.getD b 0) = 0

/-- **Every child is proven**: its deferred claim has the bytecode's shape, and the deferring
verifier (`verifyDeferred`, the guest program's `verify_sub`) accepts its proof for its statement's
digest under the same seed. The deferring verifier reads only the bytecode's length: it takes the
bytecode's value at the child's point from the witness (`freshClaim`), which the batching carries
to the root. -/
def ChildrenProven (bytecode : List K) (seed : Digest) (witness : NodeWitness) : Prop :=
  ∀ child ∈ witness.children, child.statement.deferredClaim.HasBytecodeShape bytecode ∧
    verifyDeferred bytecode seed (statementDigest seed child.statement) child.freshClaim
      child.proof = true

/-- **The deferred claim batches the children's**: without children, the bytecode at the zero
point; with children, the batching program (`Batch.nodeBatchingProgram`), over Keccak-f[1600],
accepts the stream of the children's claims (each child's public input, fresh claim and deferred
claim) and the hints, with the statement's deferred claim as its outcome. -/
def DeferredClaimBatched (bytecode : List K) (seed : Digest) (statement : NodeStatement)
    (witness : NodeWitness) : Prop :=
  if witness.children = [] then statement.deferredClaim.HasZeroPoint bytecode
  else Guest.Batch.runBatching (m := Id) keccakF1600
    (Guest.Batch.nodeBatchingProgram (· = statement.deferredClaim) bytecode
      witness.children.length)
    ⟨Guest.Batch.batchingStream (witness.children.map fun child ↦
      ⟨statementDigest seed child.statement, child.freshClaim, child.statement.deferredClaim⟩)
      witness.batchingHints, []⟩ = true

end

/-! ## What a proof of the guest program establishes, its witness named -/

/-- What a decoder names on an execution: a seed, a statement and a witness. -/
structure SeedStatementAndWitness where
  /-- The seed of the statement's digest. -/
  seed : Digest
  /-- The node statement. -/
  statement : NodeStatement
  /-- Its witness. -/
  witness : NodeWitness

/-- **The decoding explains the public input `input`**: its seed and statement have the input's
digest (the statement is the one the input commits to), and its witness covers that statement's
claims (`NodeRelation`). `GuestKnowledge` (`Theorems.lean`) says this of what the decoder program
outputs on every valid execution. -/
def ExplainsPublicInput (guest : LeanIsaProgram) (input : PublicInput)
    (decoding : SeedStatementAndWitness) : Prop :=
  statementDigest decoding.seed decoding.statement = publicInputDigest input ∧
    NodeRelation (bytecodeWords guest) decoding.seed decoding.statement decoding.witness

/-- **The candidate collisions** of two statements' digests: the pairs of inputs of the three
hashes the digests compute, the outer one and the two claim lists'. The DA digest enters the
preimage as it is. -/
def collisionCandidates (seed : Digest) (statement : NodeStatement) (seed' : Digest)
    (statement' : NodeStatement) : List (List UInt8 × List UInt8) :=
  [(statementPreimage seed statement, statementPreimage seed' statement'),
    (claimListPreimage statement.claims.xmss, claimListPreimage statement'.claims.xmss),
    (claimListPreimage statement.claims.sphincs, claimListPreimage statement'.claims.sphincs)]

/-- **A collision**: a pair of different inputs with the same Keccak-256 digest, among
`pairs`. -/
def HasCollision (pairs : List (List UInt8 × List UInt8)) : Prop :=
  ∃ p ∈ pairs, p.1 ≠ p.2 ∧ keccak256 p.1 = keccak256 p.2

/-- **The statement's digest binds the seed and the statement**: two statements whose deferred
claims have the shape of one bytecode and whose digests (under two seeds) are equal are the same
statement under the same seed, or one of the candidate pairs is a Keccak-256 collision. The shape
fixes the length of the deferred claim's point, which the digest does not record. Proved by
`LeanVM.Guest.Binding.digest_binds`. -/
def StatementDigestBinds : Prop :=
  ∀ (bytecode : List K) (seed seed' : Digest) (statement statement' : NodeStatement),
    statement.deferredClaim.HasBytecodeShape bytecode →
    statement'.deferredClaim.HasBytecodeShape bytecode →
    statementDigest seed statement = statementDigest seed' statement' →
    (seed = seed' ∧ statement = statement') ∨
      HasCollision (collisionCandidates seed statement seed' statement')

/-- The guest program's deployed seed: its Fiat-Shamir IV (`fs_seed`,
`crates/leanvm_core/src/cpu/mod.rs:63-67`). -/
abbrev deployedSeed (guest : LeanIsaProgram) : Digest := fiatShamirIv (bytecodeWords guest)

end LeanVM.Node

namespace LeanVM.Guest

/-- **The deployed leanISA guest program**, assembled from the generated `Statement/Data/`. -/
def guestProgram : LeanVM.Semantics.LeanIsaProgram := assemble Data.functions 19 (by decide)

end LeanVM.Guest

end
