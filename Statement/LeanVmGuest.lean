module

public import Statement.LeanVmGuestBatching
public import Statement.LeanXmss
public import Statement.LeanSphincs
public import Statement.LeanDa
public import Statement.Data.Bytecode
public import Statement.Fast.Schemes

/-!
# The leanISA guest program: what a node proves

A node of the aggregation has claims (`NodeStatement`: leanXMSS and leanSPHINCS claims, a DA
digest, and a claim on the guest program's bytecode it defers) and witnesses (`NodeWitness`: raw
signatures, a blob matrix, children carrying proofs, the batching's hints). What a valid execution
of the guest program establishes is that the witnesses hold the claims, `NodeRelation`:

* `SignatureClaimsHeld`: every leanXMSS and leanSPHINCS claim is held by a raw signature that
  verifies, or by a child whose statement lists it;
* `DaDigestHeld`: the DA digest is that of the blob matrix the node checks, zeros, or a child's;
* `ChildrenProven`: every child's proof is accepted, for the child's statement, by the deferring
  verifier, which takes the bytecode's value at the child's point from the witness;
* `DeferredClaimBatched`: the node's claim on the bytecode batches its children's (that value is
  checked only at the root, in the batched claim);

and the node's own claim on the bytecode has the bytecode's shape.

The node's public input is its statement's digest under a seed (`statementDigest`). After the
relation: what a decoding of an execution explains (`ExplainsPublicInput`, of which
`GuestKnowledgeSoundness`, `Theorems.lean`, is the end statement) and the binding of the statement's
digest (`StatementDigestBinds`). The batching program (`Batch.nodeBatchingProgram`), reference
material, is `LeanVmGuestBatching.lean`'s; the completeness side is `LeanVmGuestCompleteness.lean`.

Transcribed from leanVM at the pin (`../leanvm-rev`): `crates/rec_aggregation/src/aggregation.rs`
(the statement, its digest, the batching) and `crates/rec_aggregation/guests/lean_ethereum.py`
(the guest program); `aggregation.rs:N` and `lean_ethereum.py:N` are lines of those files at the
pin. The signature schemes are `LeanXmss.lean`'s and `LeanSphincs.lean`'s with Keccak-256 as their
hash; LeanDA is `LeanDa.lean`'s.

The witness is the knowledge content: "some signature verifies" says little (some signature
verifies for almost every key and message). The soundness statement takes the decoder that names
the witness as a parameter, a program of the cost machine run within a budget
(`GuestKnowledgeSoundness`). A program that output another statement of the same digest would
exhibit a Keccak-256 collision; what excludes it is that none is known. That the root's statement
makes every claim held at the leaves is not proved: it would need the Keccak computed inside the
guest program to behave as the random permutation of `LeanVM.KnowledgeSoundness`.
-/

@[expose] public section

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The claims -/

/-- A leanXMSS key and a message it signed, at a leaf index the claim does not record
(`LeanXmssClaim`, `aggregation.rs:63`). -/
abbrev LeanXmssClaim : Type := HashSig.PublicKey × HashSig.Message

/-- A leanSPHINCS key and a message it signed (`LeanSphincsClaim`, `aggregation.rs:66`). -/
abbrev LeanSphincsClaim : Type := Sphincs.PublicKey × Sphincs.Message

/-- **A DA claim**: a blob matrix's Merkle root (an aggregate's `da_root`,
`aggregation.rs:392-394`) and the digest of the vector its rows are orthogonal to. A statement
carries the claim's digest (`daClaimDigest`). -/
structure DaClaim where
  /-- The matrix's Merkle root: the commitment to its codewords. -/
  daRoot : Digest
  /-- The digest of the vector, which the guest program takes from `da_verify`'s run; the deployed
  outer verifier derives it as `vector_digest(membership_vector(root))` (`da_digest`,
  `aggregation.rs:553-557`; `crates/verifier/src/da.rs:98-103`). -/
  membershipVectorDigest : Digest
  deriving DecidableEq, Inhabited

/-- A node's claims: leanXMSS claims, leanSPHINCS claims, and its DA digest: a DA claim's
`daClaimDigest`, or `zeroDigest` without one (`da_digest`, `aggregation.rs:550-557`). -/
structure NodeClaims where
  /-- The leanXMSS claims. -/
  xmss : List LeanXmssClaim
  /-- The leanSPHINCS claims. -/
  sphincs : List LeanSphincsClaim
  /-- The DA digest. -/
  daDigest : Digest
/-- A node's statement: its claims and its deferred claim. -/
structure NodeStatement where
  /-- Its signature and DA claims. -/
  claims : NodeClaims
  /-- The claim on the bytecode it defers to its parent. -/
  deferredClaim : DeferredClaim

/-! ## The statement's digest

Each digest is Keccak-256 of its preimage; the preimages are also the inputs of the candidate
collisions (`collisionCandidates`, below). -/

/-- A claim as the `64` bytes its list hashes: the key's root and parameter, then the message
(`claim_cells`, `aggregation.rs:217-224`). -/
def claimBytes (root parameter : BitVec 128) (message : BitVec 256) : List UInt8 :=
  HashSig.littleEndianBytes 16 root ++ HashSig.littleEndianBytes 16 parameter ++
    HashSig.littleEndianBytes 32 message

/-- The bytes `claimListDigest claims` hashes. Both schemes' keys are a root and a parameter
(`LeanXmssClaim` and `LeanSphincsClaim` are one type). -/
def claimListPreimage (claims : List LeanXmssClaim) : List UInt8 :=
  claims.flatMap fun claim ↦ claimBytes claim.1.root claim.1.parameter claim.2

/-- The digest of a list of leanXMSS or leanSPHINCS claims (`claim_list_digest`,
`aggregation.rs:211-213`, `lean_ethereum.py:3822-3844`). -/
def claimListDigest (claims : List LeanXmssClaim) : Digest := keccak256 (claimListPreimage claims)

/-- The bytes `daClaimDigest claim` hashes: the root, then the vector digest. -/
def daClaimPreimage (claim : DaClaim) : List UInt8 :=
  digestBytes claim.daRoot ++ digestBytes claim.membershipVectorDigest

/-- A DA claim's digest, which a statement carries (`root_vector_digest`,
`aggregation.rs:559-562`; the guest program's `keccak([root_0, root_1], [vector_0, vector_1])`,
`lean_ethereum.py:4164`). -/
def daClaimDigest (claim : DaClaim) : Digest := keccak256 (daClaimPreimage claim)

/-- The DA digest of a statement without a DA claim: zeros (`da_digest(None)`,
`aggregation.rs:553-557`; `own_da`'s zero cells, `lean_ethereum.py:4166-4167`). -/
def zeroDigest : Digest := Vector.replicate 4 0

/-- The deferred claim's cells, an odd count paired with a zero cell. -/
def paddedDeferredClaimCells (claim : DeferredClaim) : List E :=
  claim.cells ++ if claim.cells.length % 2 = 1 then [0] else []

/-- The bytes `statementDigest seed statement` hashes: the seed, the leanXMSS and leanSPHINCS
claims' digests, the DA digest, then the padded deferred cells. Each list's digest binds its length
through Keccak's padding. -/
def statementPreimage (seed : Digest) (statement : NodeStatement) : List UInt8 :=
  digestBytes seed ++ digestBytes (claimListDigest statement.claims.xmss) ++
    digestBytes (claimListDigest statement.claims.sphincs) ++
    digestBytes statement.claims.daDigest ++
    (paddedDeferredClaimCells statement.deferredClaim).flatMap E.toBytes

/-- **The statement's digest under `seed`**, a node's public input (`statement_digest`,
`aggregation.rs:331-360`, `lean_ethereum.py:3759-3790`). The cells carry no lengths: the digest
tells two deferred claims apart only at one shape. -/
def statementDigest (seed : Digest) (statement : NodeStatement) : Digest :=
  keccak256 (statementPreimage seed statement)

end LeanVM.Node

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

/-- How a node holds a signature claim: by a raw signature, or through its `childIndex`-th child. -/
inductive ClaimHolder (Signature : Type) where
  /-- By a raw signature. -/
  | signature (signature : Signature)
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
  SignatureClaimsHeld statement witness ∧ DaDigestHeld statement witness ∧
    ChildrenProven bytecode seed witness ∧ DeferredClaimBatched bytecode seed statement witness ∧
    statement.deferredClaim.HasBytecodeShape bytecode

/-- **Every signature claim is held**: the `i`-th leanXMSS claim by the `i`-th leanXMSS
holder, a raw signature that verifies at any leaf index or a child whose statement lists the
claim; likewise for leanSPHINCS. Holders need not differ: one child may hold several claims. -/
def SignatureClaimsHeld (statement : NodeStatement) (witness : NodeWitness) : Prop :=
  List.Forall₂ (ClaimIsHeld (fun (claim : LeanXmssClaim) signature ↦
      LeanXmss.verifyWithKeccak claim.1 claim.2 signature = true) NodeClaims.xmss witness.children)
    statement.claims.xmss witness.xmssHolders ∧
  List.Forall₂ (ClaimIsHeld (fun (claim : LeanSphincsClaim) signature ↦
      Sphincs.verifyWithKeccak claim.1 claim.2 signature = true) NodeClaims.sphincs
      witness.children)
    statement.claims.sphincs witness.sphincsHolders

/-- **A claim is held** by a holder: a raw signature that `holds` it, or a child whose claims of
the kind (`claimsOf`) list it. -/
def ClaimIsHeld {Claim Signature : Type} (holds : Claim → Signature → Prop)
    (claimsOf : NodeClaims → List Claim) (children : List Child) (claim : Claim) :
    ClaimHolder Signature → Prop
  | .signature signature => holds claim signature
  | .child childIndex =>
    ∃ child, children[childIndex]? = some child ∧ claim ∈ claimsOf child.statement.claims

/-- **The DA digest is held**: it is the digest of the DA claim that the matrix checked here
opens; without such a matrix, zero or some child's DA digest (`da_pick`,
`lean_ethereum.py:4202-4206`). -/
def DaDigestHeld (statement : NodeStatement) (witness : NodeWitness) : Prop :=
  match witness.daMatrix with
  | some (claim, matrix) =>
    statement.claims.daDigest = daClaimDigest claim ∧
      LeanVM.Da.MatrixWitness.Opens claim.daRoot claim.membershipVectorDigest matrix
  | none =>
    statement.claims.daDigest = zeroDigest ∨
      ∃ child ∈ witness.children, child.statement.claims.daDigest = statement.claims.daDigest

/-- **The matrix opens the DA claim `⟨root, vectorDigest⟩`** (`da_verify`,
`lean_ethereum.py:3915-4053`): `1` to `1024` codewords of `2^15` symbols commit to `root` (the
root of the matrix they form, `LeanDa.commitCells`), each is orthogonal to the vector, and the
vector's digest is `vectorDigest` (two-level, `LeanDa.vectorDigest`, `da_vector_cell`,
`lean_ethereum.py:4043-4053`), all over Keccak-f[1600]
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
    LeanDa.commitCells keccakF1600 (LeanDa.cellsOfRows witness.rows) = root.toBytes ∧
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
digest (the statement is the one the input commits to), and its witness holds that statement's
claims (`NodeRelation`). `GuestKnowledgeSoundness` (`Theorems.lean`) says this of what the decoder
program outputs on every valid execution. -/
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
