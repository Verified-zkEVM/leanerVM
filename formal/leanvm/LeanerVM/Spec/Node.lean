/-
  LeanerVM.Spec.Node

  What one node of an aggregation tree establishes: the statement of the aggregation guest,
  its encodings, the claims it defers, and `NodeSpec`.
-/

module

public import LeanerVM.Spec.Statement
public import LeanerVM.Spec.Xmss
public import LeanerVM.Spec.Sphincs
public import LeanerVM.Spec.Da

/-!
# The aggregation node

**Status: stated, not proved.** No theorem of the repository is about these definitions yet.

Category B: transcribed from leanVM `a0ca7858f2533ce51abdc20bb635c007e19b26b3`,
`crates/rec_aggregation/src/aggregation.rs` (the statement, its digest, the outer verifier) and
`crates/rec_aggregation/guests/lean_ethereum.py` (the guest).

A node's statement is a list of signature claims, a list of DA claims, and a claim on the
polynomials that the protocol fixes (the guest's bytecode, flock's matrices), which the node
defers rather than evaluates (`NodeStatement`). Its public input is the statement's digest under
a seed, the guest's Fiat–Shamir IV (`statementDigest`).

A node holds every claim either directly, by an XMSS or SPHINCS signature or a blob matrix, or
through a child that makes the same claim. A child is a statement under the same seed and a
proof that the deferring verifier accepts for it
(`LeanerVM.Protocol.Verifier.verifyDeferred`). The node batches the claims that its children's
proofs make of the fixed polynomials, with those its children's statements defer, into its own
deferred claim (`batch`). `NodeRel bytecode seed s w` says all of it of the statement `s`, with
the witness `w` holding every claim; `NodeSpec` is its existential.

The outer verifier (`verifyAggregate`) checks a proof of the guest on the statement's digest and
evaluates the deferred claim itself.

What a valid execution of the guest establishes is `NodeSpec`, on BLAKE2s, as the guest computes
it. The witness is the knowledge content: on its own, "some signature verifies" says little, since
some signature verifies for almost every key and message. That the root's `NodeSpec` makes every
claim held at the leaves is a separate argument, conditional on a heuristic: a child's proof is
sound only if BLAKE2s, computed inside the guest, behaves as the random oracle of
`LeanVM.KnowledgeSoundness`.
-/

namespace LeanVM.Node

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.Compile LeanerVM.Protocol.Verifier

@[expose] public section

/-! ## The signature schemes on BLAKE2s -/

/-- BLAKE2s-256 as the schemes' hash: its 32 bytes as a little-endian 256-bit vector. -/
def blake2sBits (input : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 ((digestBytes (blake2sBytes input)).foldr (fun b acc ↦ b.toNat + 256 * acc) 0)

/-- XMSS verification with BLAKE2s. -/
def xmssVerify (pk : XmssSecurity.PublicKey) (leafIndex : XmssSecurity.LeafIndex)
    (message : XmssSecurity.Message) (σ : XmssSecurity.Signature) : Bool :=
  letI : HasQuery XmssSecurity.HashSpec Id := ⟨blake2sBits⟩
  Id.run (XmssSecurity.Concrete.verify pk leafIndex message σ)

/-- SPHINCS verification with BLAKE2s. -/
def sphincsVerify (pk : Sphincs.PublicKey) (message : Sphincs.Message) (σ : Sphincs.Signature) :
    Bool :=
  letI : HasQuery Sphincs.HashSpec Id := ⟨blake2sBits⟩
  Id.run (Sphincs.Concrete.verify pk message σ)

/-! ## The statement -/

/-- XMSS signers that signed one message at one leaf index (`XmssClaimGroup`). The leaf index is
the 128-bit cell the statement carries; the guest bounds it below `2^32` only where it verifies
a signature at it. -/
structure XmssGroup where
  /-- The leaf index. -/
  leafIndex : BitVec 128
  /-- The message. -/
  message : XmssSecurity.Message
  /-- The keys. -/
  keys : List XmssSecurity.PublicKey

/-- A SPHINCS key and a message it signed (`SphincsClaim`). -/
abbrev SphincsClaim : Type := Sphincs.PublicKey × Sphincs.Message

/-- A DA claim: a root and the digest of the vector its rows are orthogonal to. -/
abbrev DaClaim : Type := Digest × Digest

/-- A node's claims: XMSS signers by leaf index and message, SPHINCS signers, and DA claims. -/
structure Claims where
  /-- The XMSS groups. -/
  xmss : List XmssGroup
  /-- The SPHINCS claims. -/
  sphincs : List SphincsClaim
  /-- The DA claims. -/
  da : List DaClaim

/-- The claim the statement defers on the fixed polynomials: the bytecode's value at a point,
and the values of flock's matrices `A0`, `B0` at one point (`DeferredClaim`). -/
structure DeferredClaim where
  /-- The bytecode's point. -/
  bytecodePoint : List E
  /-- The bytecode's value there. -/
  bytecodeValue : E
  /-- The matrices' point: row coordinates, then column coordinates. -/
  matrixPoint : List E
  /-- `A0`'s value there. -/
  matrixA : E
  /-- `B0`'s value there. -/
  matrixB : E

/-- A node's statement: its claims and its deferred claim. -/
structure NodeStatement where
  /-- The claims. -/
  claims : Claims
  /-- The deferred claim. -/
  defer : DeferredClaim

/-! ## The deferred claim -/

/-- The deferred claim has the shape of the bytecode `bytecode`: a point of `log₂` of its length
on the bytecode, and one of `2 · blake2sR1csLogSize` coordinates on the matrices
(`BYTECODE_VARS`, `2 · K_LOG`). -/
def DeferredClaim.Shaped (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.bytecodePoint.length = Nat.log2 bytecode.length ∧
    c.matrixPoint.length = 2 * blake2sR1csLogSize

/-- The multilinear extensions of `A0` and `B0` at a point, its first `blake2sR1csLogSize`
coordinates the row (`verifier::deferred::matrix_values`). -/
def matrixValues (point : List E) : E × E :=
  let (left, right) := blake2sRowValues (eqKernel (point.drop blake2sR1csLogSize))
  (multilinearEval left.toList (point.take blake2sR1csLogSize),
    multilinearEval right.toList (point.take blake2sR1csLogSize))

/-- **The deferred claim is true** of the bytecode `bytecode`: it has the shape, and the values
are the polynomials' at the points (`DeferredClaim::recompute_scalar`). -/
def DeferredClaim.Holds (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.Shaped bytecode ∧ 2 ^ c.bytecodePoint.length = bytecode.length ∧
    multilinearEval (bytecode.map ofK) c.bytecodePoint = c.bytecodeValue ∧
    matrixValues c.matrixPoint = (c.matrixA, c.matrixB)

/-- What a leaf defers: the polynomials at the all-zero points (`DeferredClaim::leaf`). The
values are the outer verifier's to check. -/
def DeferredClaim.AtZero (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.bytecodePoint = List.replicate (Nat.log2 bytecode.length) 0 ∧
    c.matrixPoint = List.replicate (2 * blake2sR1csLogSize) 0

/-- The cells a deferred claim is hashed and absorbed as, in the guest's `defer_stmt` order. -/
def DeferredClaim.cells (c : DeferredClaim) : List E :=
  c.bytecodePoint ++ [c.bytecodeValue] ++ c.matrixPoint ++ [c.matrixA, c.matrixB]

/-- The cells of a proof's claims on the fixed polynomials, in the order the guest exports them
(`verify_sub`'s `defer_out`): the lincheck's column point in round order. -/
def fixedCells (c : FixedClaims) : List E :=
  c.bytecodePoint ++ [c.bytecodeValue, c.alpha, c.zSkip] ++ c.rowPoint ++ c.columnPoint.reverse ++
    c.slices ++ [c.matrixValue]

/-! ## The statement's digest -/

/-- The 16 bytes of a 128-bit value, least significant byte first: a cell's two limbs. -/
def bytes16 (value : BitVec 128) : List UInt8 := XmssSecurity.bytesLE 16 value

/-- A count as the statement carries it: `g^n` in the low limb of a cell (`scalar_count`). -/
def countBytes (n : ℕ) : List UInt8 := kBytes (gpow n) ++ kBytes 0

/-- The digest of one group's keys, `32` bytes a key: its root, then its parameter
(`key_list_digest`). -/
def keyListDigest (keys : List XmssSecurity.PublicKey) : Digest :=
  blake2sBytes (keys.flatMap fun pk ↦ bytes16 pk.root ++ bytes16 pk.parameter)

/-- The digest of the SPHINCS claims, `64` bytes a claim: the key's root and parameter, then the
message (`sphincs_list_digest`). -/
def sphincsListDigest (claims : List SphincsClaim) : Digest :=
  blake2sBytes (claims.flatMap fun c ↦
    bytes16 c.1.root ++ bytes16 c.1.parameter ++ XmssSecurity.bytesLE 32 c.2)

/-- **The signer set's digest** (`signers_hash`): both lengths and the SPHINCS list's digest,
then two blocks a group, its leaf index, key count and message, then its keys' digest. -/
def signersDigest (xmss : List XmssGroup) (sphincs : List SphincsClaim) : Digest :=
  blake2sBytes (countBytes xmss.length ++ countBytes sphincs.length ++
    digestBytes (sphincsListDigest sphincs) ++
    xmss.flatMap fun group ↦
      bytes16 group.leafIndex ++ countBytes group.keys.length ++
        XmssSecurity.bytesLE 32 group.message ++ digestBytes (keyListDigest group.keys) ++
        List.replicate 32 0)

/-- The DA claims' digest: each root, then its vector digest (`da_list_digest` in the guest;
the outer verifier's `verifier::da::list_digest` derives the vector digests from the roots). -/
def daListDigest (claims : List DaClaim) : Digest :=
  blake2sBytes (claims.flatMap fun c ↦ digestBytes c.1 ++ digestBytes c.2)

/-- The 24 bytes of a field element, its three limbs. -/
def eBytes (x : E) : List UInt8 := kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2)

/-- **The statement's digest under `seed`** (`statement_digest`): the seed, the signer set's
digest and the DA claims' digest, then the deferred claim's cells, an odd count paired with a
zero cell, zero-filled to whole 64-byte blocks. The cells carry no lengths: the digest tells two
deferred claims apart only at one shape. -/
def statementDigest (seed : Digest) (s : NodeStatement) : Digest :=
  let cells := s.defer.cells ++ if s.defer.cells.length % 2 = 1 then [0] else []
  let bytes := digestBytes seed ++ digestBytes (signersDigest s.claims.xmss s.claims.sphincs) ++
    digestBytes (daListDigest s.claims.da) ++ cells.flatMap eBytes
  blake2sBytes (bytes ++ List.replicate ((64 - bytes.length % 64) % 64) 0)

/-! ## Batching the deferred claims (`aggregate_claims`, `aggregate_deferred_claims`) -/

/-- A Fiat–Shamir chain, as the transcript runs it. -/
abbrev Chain : Type → Type := StateM Digest

/-- Absorb a scalar (`obs`). -/
def observe (x : E) : Chain Unit :=
  modify fun cv ↦ blake2sBytes (digestBytes cv ++ blockOf x 1)

/-- Squeeze a challenge (`squeeze`). -/
def squeeze : Chain E := do
  let cv := blake2sBytes (digestBytes (← get) ++ blockOf 0 2)
  set cv
  return challengeOf cv

/-- The rounds of a batching sumcheck from the running claim: each round absorbs `g(1)` and
`g(∞)`, squeezes the challenge, and folds the degree-2 round polynomial whose `g(0)` the claim
fixes (`batch_sumcheck`, `absorb_round`). The challenges and the final claim. -/
def batchRounds : E → List (E × E) → Chain (List E × E)
  | claim, [] => return ([], claim)
  | claim, (g1, gInf) :: rest => do
    observe g1
    observe gInf
    let r ← squeeze
    let g0 := claim + g1
    let (rs, final) ← batchRounds ((gInf * r + (g0 + g1 + gInf)) * r + g0) rest
    return (r :: rs, final)

/-- What a node knows of one child: the child's public input, the claims its proof makes, and
the claim its statement defers. -/
structure ChildClaims where
  /-- The child's public input. -/
  publicInput : Digest
  /-- What its proof claims. -/
  fresh : FixedClaims
  /-- What its statement defers. -/
  carried : DeferredClaim

/-- The prover's part of a batching: the two sumchecks' rounds and the polynomials' values at
their ends. -/
structure BatchHints where
  /-- The bytecode sumcheck's rounds. -/
  bytecodeRounds : List (E × E)
  /-- The matrices' sumcheck's rounds. -/
  matrixRounds : List (E × E)
  /-- The bytecode's value at the end. -/
  bytecodeValue : E
  /-- `A0`'s value at the end. -/
  matrixA : E
  /-- `B0`'s value at the end. -/
  matrixB : E

/-- The weight of a proof's claim on the matrices at `r`: the multilinear extensions of the
lincheck's row and column weights at `r`'s row and column halves. -/
def freshWeight (c : FixedClaims) (r : List E) : E :=
  multilinearEval (lincheckRowWeights c.zSkip c.rowPoint) (r.take blake2sR1csLogSize) *
    multilinearEval (lincheckColumnWeights c.columnPoint c.slices) (r.drop blake2sR1csLogSize)

/-- The batching transcript's label (`RECURSION_AGG_LABEL`). -/
def batchLabel : List UInt8 := "leanvm/recursion-aggregation/v1".toUTF8.toList

/-- **The batching**: one transcript absorbs the children's public inputs and claims, then two
sumchecks reduce every child's claims to one point, for the bytecode and for the two matrices.
The claim deferred there, if both sumchecks close. -/
def batch (children : List ChildClaims) (h : BatchHints) : Option DeferredClaim :=
  go.run' (blake2sBytes batchLabel)
where
  /-- The transcript. -/
  go : Chain (Option DeferredClaim) := do
    observe (ofK (gpow children.length))
    for c in children do
      observe (digestScalars c.publicInput).1
      observe (digestScalars c.publicInput).2
      for x in fixedCells c.fresh ++ c.carried.cells do observe x
    -- the bytecode
    let mut bytecodeLambdas : List (E × E) := []
    for _ in children do
      let lf ← squeeze
      let lc ← squeeze
      bytecodeLambdas := bytecodeLambdas ++ [(lf, lc)]
    let bytecodeClaim := sumE (List.zipWith (fun c l ↦
      l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) children bytecodeLambdas)
    let (rBytecode, bytecodeFinal) ← batchRounds bytecodeClaim h.bytecodeRounds
    let bytecodeWeight := sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.fresh.bytecodePoint rBytecode +
        l.2 * eqEval c.carried.bytecodePoint rBytecode) children bytecodeLambdas)
    -- the matrices
    let mut matrixLambdas : List (E × E × E) := []
    for _ in children do
      let lf ← squeeze
      let la ← squeeze
      let lb ← squeeze
      matrixLambdas := matrixLambdas ++ [(lf, la, lb)]
    let matrixClaim := sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.matrixValue +
      l.2.1 * c.carried.matrixA + l.2.2 * c.carried.matrixB) children matrixLambdas)
    let (rMatrix, matrixFinal) ← batchRounds matrixClaim h.matrixRounds
    let weightA := sumE (List.zipWith (fun c l ↦ l.1 * freshWeight c.fresh rMatrix +
      l.2.1 * eqEval c.carried.matrixPoint rMatrix) children matrixLambdas)
    let weightB := sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.alpha * freshWeight c.fresh rMatrix +
      l.2.2 * eqEval c.carried.matrixPoint rMatrix) children matrixLambdas)
    if bytecodeFinal = h.bytecodeValue * bytecodeWeight ∧
        matrixFinal = h.matrixA * weightA + h.matrixB * weightB then
      return some ⟨rBytecode, h.bytecodeValue, rMatrix, h.matrixA, h.matrixB⟩
    else return none

/-! ## The node -/

/-- A child of a node: its statement, its proof, and what the proof claims of the fixed
polynomials. -/
structure Child where
  /-- The child's statement. -/
  statement : NodeStatement
  /-- What its proof claims. -/
  fresh : FixedClaims
  /-- Its proof. -/
  proof : Proof

/-- How a node holds a claim: directly, by a witness, or through its `i`-th child. -/
inductive Holder (W : Type) where
  /-- By a witness. -/
  | direct (w : W)
  /-- Through child `i`. -/
  | child (i : ℕ)

/-- What a node holds its statement by: its children, a holder for every claim (per XMSS group,
one per key), and the batching's hints. -/
structure NodeWitness where
  /-- The children. -/
  children : List Child
  /-- The XMSS claims' holders. -/
  xmss : List (List (Holder XmssSecurity.Signature))
  /-- The SPHINCS claims' holders. -/
  sphincs : List (Holder Sphincs.Signature)
  /-- The DA claims' holders. -/
  da : List (Holder Da.Witness)
  /-- The batching's hints. -/
  hints : BatchHints

/-- The XMSS key `pk` of `group` is held: by a signature at the group's leaf index, which is
below `2^32`, and message, or by a child's group of the same leaf index and message. -/
def XmssHeld (children : List Child) (group : XmssGroup) (pk : XmssSecurity.PublicKey) :
    Holder XmssSecurity.Signature → Prop
  | .direct σ => ∃ h : group.leafIndex.toNat < XmssSecurity.lifetime,
      xmssVerify pk ⟨group.leafIndex.toNat, h⟩ group.message σ = true
  | .child i => ∃ c, children[i]? = some c ∧ ∃ group' ∈ c.statement.claims.xmss,
      group'.leafIndex = group.leafIndex ∧ group'.message = group.message ∧ pk ∈ group'.keys

/-- The SPHINCS claim is held: by a signature, or by a child making it. -/
def SphincsHeld (children : List Child) (claim : SphincsClaim) :
    Holder Sphincs.Signature → Prop
  | .direct σ => sphincsVerify claim.1 claim.2 σ = true
  | .child i => ∃ c, children[i]? = some c ∧ claim ∈ c.statement.claims.sphincs

/-- The DA claim is held: by a matrix, or by a child making it. -/
def DaHeld (children : List Child) (claim : DaClaim) : Holder Da.Witness → Prop
  | .direct w => w.Opens claim.1 claim.2
  | .child i => ∃ c, children[i]? = some c ∧ claim ∈ c.statement.claims.da

/-- **What the witness `w` establishes of a node's statement `s`**, for the guest `bytecode` and
under the seed `seed`:
* every deferred claim, the node's and its children's, has the bytecode's shape;
* the deferring verifier accepts every child's proof, for the child's statement under the same
  seed;
* every claim of `s` is held;
* `s` defers the batching of the children's claims on the fixed polynomials, and a node without
  children the polynomials at zero. -/
def NodeRel (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) : Prop :=
  s.defer.Shaped bytecode ∧
  (∀ c ∈ w.children, c.statement.defer.Shaped bytecode ∧
    verifyDeferred bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true) ∧
  List.Forall₂ (fun group holders ↦ List.Forall₂ (XmssHeld w.children group) group.keys holders)
    s.claims.xmss w.xmss ∧
  List.Forall₂ (SphincsHeld w.children) s.claims.sphincs w.sphincs ∧
  List.Forall₂ (DaHeld w.children) s.claims.da w.da ∧
  if w.children = [] then s.defer.AtZero bytecode
  else batch (w.children.map fun c ↦
    ⟨statementDigest seed c.statement, c.fresh, c.statement.defer⟩) w.hints = some s.defer

/-- **What a node of the aggregation guest `bytecode` establishes of its statement `s`** under
the seed `seed`: a witness holds it. -/
def NodeSpec (bytecode : List K) (seed : Digest) (s : NodeStatement) : Prop :=
  ∃ w, NodeRel bytecode seed s w

/-! ## The outer verifier -/

/-- **The outer verifier** of an aggregate of the guest `guest` (`EthereumProof::verify`): every
DA claim's vector digest is its root's, the deferred claim holds, and the proof verifies on the
statement's digest under the guest's IV. It omits the deployed verifier's checks on the lists'
form (`check_signer_set`, `check_da_roots`: sorted without repeats, non-empty groups, fewer than
`2^16` signature claims, at most `1024` groups and `16` DA roots), so it accepts more. -/
def verifyAggregate (guest : Program) (s : NodeStatement) (π : Proof) : Prop :=
  (∀ c ∈ s.claims.da, c.2 = Da.vectorDigest (Da.membershipVector c.1)) ∧
    s.defer.Holds (bytecodeWords guest) ∧
    Verifier.verify (bytecodeWords guest)
      (statementDigest (fiatShamirIv (bytecodeWords guest)) s) π = true

end
end LeanVM.Node
