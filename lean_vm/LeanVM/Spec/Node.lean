/-
  LeanVM.Spec.Node

  What one node of an aggregation tree establishes: the statement of the aggregation guest,
  its encodings, the claim it defers, and `NodeSpec`.
-/

module

public import LeanVM.Spec.Statement
public import LeanXmss.Scheme
public import Sphincs.Scheme
public import LeanVM.Spec.Da
public import LeanVM.Spec.Fast.Schemes

/-!
# The aggregation node

Transcribed from leanVM `3375f7a137c50b803f3416f6466b5d4e0719708a` (branch `keccak-gkr`),
`crates/rec_aggregation/src/aggregation.rs` (the statement, its digest, the batching, the outer
verifier) and `crates/rec_aggregation/guests/lean_ethereum.py` (the guest); `aggregation.rs:N`
and `lean_ethereum.py:N` below are lines of those files at that commit. The signature schemes,
leanXMSS and leanSPHINCS, are those whose security `lean_xmss` and `lean_sphincs` prove, imported
from their `Scheme` modules, with Keccak-256 as their hash; LeanDA is `lean_da`'s
(`LeanVM.Spec.Da`).

A node's statement is a list of signature claims, a list of DA claims, and a claim on the
polynomial that the protocol fixes, the guest's stacked bytecode, which the node defers rather
than evaluates (`NodeStatement`). Its public input is the statement's digest under a seed, the
guest's Fiat-Shamir IV (`statementDigest`, `statement_digest`, `aggregation.rs:344-365`,
`lean_ethereum.py:3766-3797`): the Keccak-256 hash of the seed, the signer set's digest and the
DA claims' digest, sixteen bytes a cell, then the deferred claim's cells, three limbs each.

A node holds every claim either directly, by a leanXMSS or leanSPHINCS signature or a blob
matrix, or through a child that makes the same claim. A child is a statement under the same seed
and a proof that the deferring verifier accepts for it
(`LeanVM.Protocol.Verifier.verifyDeferred`, the guest's `verify_sub`). The node batches the
claims that its children's proofs make of the bytecode, with those its children's statements
defer, into its own deferred claim (`batch`: `aggregate_claims`, `lean_ethereum.py:4285-4392`;
`aggregate_deferred_claims`, `aggregation.rs:943-1056`). `NodeRel bytecode seed s w` says all
of it of the statement `s`, with the witness `w` holding every claim; `NodeSpec` is its
existential.

The outer verifier (`verifyAggregate`, `EthereumProof::verify`, `aggregation.rs:695-717`) checks
a proof of the guest on the statement's digest and evaluates the deferred claim itself.

What a valid execution of the guest establishes is `NodeRel` of the witness its memory holds, on
Keccak, as the guest computes it (`Guest.lean`: `GuestKnowledge`, with a decoder). The witness is
the knowledge content: `NodeSpec` alone, "some signature verifies", says little, since some
signature verifies for almost every key and message. That the root's `NodeSpec` makes every
claim held at the leaves is a separate argument, conditional on a heuristic: a child's proof is
sound only if Keccak, computed inside the guest, behaves as the random oracles of
`LeanVM.KnowledgeSoundness`.

**Changes from the leanVM `3f7dc219` transcription.** BLAKE2s is replaced by Keccak-256 (the
hashes) and Keccak-f[1600] (the batching's transcript, a duplex sponge). Flock is gone, so the
deferred claim is the bytecode's alone: a point and a value (`DeferredClaim`,
`aggregation.rs:258-318`), and a proof's claims on the fixed polynomials are its bytecode claim
(`FixedClaims`). The statement's preimage is no longer zero-filled to whole blocks. The batching
runs on the verifier's duplex sponge from the label's hash (`FiatShamirState::from_label`), each
group of absorbed words padded with zeros to a whole rate, and reduces both claims of every child
by one sumcheck.
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The signature schemes on Keccak-256 -/

/-- A digest as the schemes' 256-bit hash output: its 32 bytes as a little-endian number. -/
def digestBits (d : Digest) : BitVec 256 :=
  BitVec.ofNat 256 ((digestBytes d).foldr (fun b acc ↦ b.toNat + 256 * acc) 0)

/-- Keccak-256 as the schemes' hash. -/
def keccakBits (input : List UInt8) : BitVec 256 := digestBits (keccak256 input)

/-- leanXMSS verification with Keccak-256. The leaf index is the signature's. -/
def xmssVerify (pk : LeanXmss.PublicKey) (message : LeanXmss.Message) (σ : LeanXmss.Signature) :
    Bool :=
  letI : HasQuery LeanXmss.HashSpec Id := ⟨keccakBits⟩
  Id.run (LeanXmss.Concrete.verify pk message σ)

/-- leanSPHINCS verification with Keccak-256. -/
def sphincsVerify (pk : Sphincs.PublicKey) (message : Sphincs.Message) (σ : Sphincs.Signature) :
    Bool :=
  letI : HasQuery Sphincs.HashSpec Id := ⟨keccakBits⟩
  Id.run (Sphincs.Concrete.verify pk message σ)

/-! ## The statement -/

/-- A leanXMSS key and a message it signed, at a leaf index the claim does not record
(`LeanXmssClaim`, `aggregation.rs:60`). -/
abbrev XmssClaim : Type := LeanXmss.PublicKey × LeanXmss.Message

/-- A leanSPHINCS key and a message it signed (`LeanSphincsClaim`, `aggregation.rs:63`). -/
abbrev SphincsClaim : Type := Sphincs.PublicKey × Sphincs.Message

/-- A DA claim: a root and the digest of the vector its rows are orthogonal to. -/
abbrev DaClaim : Type := Digest × Digest

/-- A node's claims: leanXMSS claims, leanSPHINCS claims, and DA claims. -/
structure Claims where
  /-- The leanXMSS claims. -/
  xmss : List XmssClaim
  /-- The leanSPHINCS claims. -/
  sphincs : List SphincsClaim
  /-- The DA claims. -/
  da : List DaClaim

/-- The claim the statement defers on the stacked bytecode: its value at a point
(`DeferredClaim`, `aggregation.rs:258-261`). -/
structure DeferredClaim where
  /-- The bytecode's point. -/
  bytecodePoint : List E
  /-- The bytecode's value there. -/
  bytecodeValue : E

/-- A node's statement: its claims and its deferred claim. -/
structure NodeStatement where
  /-- The claims. -/
  claims : Claims
  /-- The deferred claim. -/
  defer : DeferredClaim

/-! ## The deferred claim -/

/-- The deferred claim has the shape of the bytecode `bytecode`: a point of `log₂` of its length
(`bytecode_vars`, `aggregation.rs:822-824`; `BYTECODE_VARS`, `lean_ethereum.py:330`). -/
def DeferredClaim.Shaped (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.bytecodePoint.length = Nat.log2 bytecode.length

/-- **The deferred claim is true** of the bytecode `bytecode`: it has the shape, and the value is
the bytecode's multilinear extension at the point (`DeferredClaim::recompute_scalar`,
`aggregation.rs:279-311`). -/
def DeferredClaim.Holds (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.Shaped bytecode ∧ 2 ^ c.bytecodePoint.length = bytecode.length ∧
    multilinearEval (bytecode.map ofK) c.bytecodePoint = c.bytecodeValue

/-- What a leaf defers: the bytecode at the all-zero point (`DeferredClaim::leaf`,
`aggregation.rs:266-268`; `main`'s leaf branch, `lean_ethereum.py:4266-4274`). The value is
the outer verifier's to check. -/
def DeferredClaim.AtZero (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.bytecodePoint = List.replicate (Nat.log2 bytecode.length) 0

/-- The cells a deferred claim is hashed and absorbed as: the point, then the value
(`DeferredClaim::cells`, `aggregation.rs:313-317`; the guest's `defer_stmt`). -/
def DeferredClaim.cells (c : DeferredClaim) : List E :=
  c.bytecodePoint ++ [c.bytecodeValue]

/-- The cells of a proof's claim on the bytecode, in the order the guest exports them
(`verify_sub`'s `defer_out`, `lean_ethereum.py:3331-3335`): the point (the bus point's row
coordinates, then the selector challenges), then the value. -/
def fixedCells (c : FixedClaims) : List E :=
  c.bytecodePoint ++ [c.bytecodeValue]

/-! ## The statement's digest -/

/-- The 16 bytes of a 128-bit value, least significant byte first: a cell's two limbs. -/
def bytes16 (value : BitVec 128) : List UInt8 := LeanXmss.bytesLE 16 value

/-- A claim as the `64` bytes its list hashes: the key's root and parameter, then the message
(`claim_cells`, `aggregation.rs:218-225`). -/
def claimBytes (root parameter : BitVec 128) (message : BitVec 256) : List UInt8 :=
  bytes16 root ++ bytes16 parameter ++ LeanXmss.bytesLE 32 message

/-- The digest of the leanXMSS claims (`claim_list_digest`, `aggregation.rs:212-214`,
`lean_ethereum.py:3827-3849`). -/
def xmssListDigest (claims : List XmssClaim) : Digest :=
  keccak256 (claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2)

/-- The digest of the leanSPHINCS claims (`claim_list_digest`). -/
def sphincsListDigest (claims : List SphincsClaim) : Digest :=
  keccak256 (claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2)

/-- **The signer set's digest** (`signers_hash`, `aggregation.rs:239-248`): the hash of the two
lists' digests. Each binds its list's length through Keccak's padding. -/
def signersDigest (xmss : List XmssClaim) (sphincs : List SphincsClaim) : Digest :=
  keccak256 (digestBytes (xmssListDigest xmss) ++ digestBytes (sphincsListDigest sphincs))

/-- The DA claims' digest: each root, then its vector digest (`da_list_digest` in the guest,
`lean_ethereum.py:4063-4075`; the outer verifier's `verifier::da::list_digest` derives the vector
digests from the roots). -/
def daListDigest (claims : List DaClaim) : Digest :=
  keccak256 (claims.flatMap fun c ↦ digestBytes c.1 ++ digestBytes c.2)

/-- The 24 bytes of a field element, its three limbs. -/
def eBytes (x : E) : List UInt8 := kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2)

/-- **The statement's digest under `seed`** (`statement_digest`, `aggregation.rs:344-365`,
`lean_ethereum.py:3766-3797`): the Keccak-256 hash of the seed, the signer set's digest and the
DA claims' digest, then the deferred claim's cells, an odd count paired with a zero cell. The
cells carry no lengths: the digest tells two deferred claims apart only at one shape. -/
def statementDigest (seed : Digest) (s : NodeStatement) : Digest :=
  let cells := s.defer.cells ++ if s.defer.cells.length % 2 = 1 then [0] else []
  keccak256 (digestBytes seed ++ digestBytes (signersDigest s.claims.xmss s.claims.sphincs) ++
    digestBytes (daListDigest s.claims.da) ++ cells.flatMap eBytes)

/-! ## Batching the deferred claims (`aggregate_claims`, `aggregate_deferred_claims`) -/

/-- A Fiat-Shamir chain: the verifier's duplex sponge over Keccak-f[1600] (`FiatShamirState`). -/
abbrev Chain : Type → Type := StateM Sponge

/-- Absorb a scalar (`observe`). -/
def observe (x : E) : Chain Unit :=
  modify fun sp ↦ Id.run (Compile.absorb (m := Id) keccakF sp x dsObserve)

/-- Squeeze a challenge (`sample`). -/
def sample : Chain E := do
  let (c, sp) := Id.run (Compile.squeeze (m := Id) keccakF (← get))
  set sp
  return c

/-- Words padded with zeros to a whole rate, `rateScalars` words (`pad`,
`aggregation.rs:953-957`; `AGG_CHILD_PAD`). -/
def padRate (words : List E) : List E :=
  words ++ List.replicate ((rateScalars - words.length % rateScalars) % rateScalars) 0

/-- The rounds of a batching sumcheck from the running claim: each round absorbs `g(1)` and
`g(∞)`, squeezes the challenge, and folds the degree-2 round polynomial whose `g(0)` the claim
fixes (`batch_sumcheck`, `lean_ethereum.py:1007-1024`; `absorb_round`,
`aggregation.rs:884-900`). The challenges and the final claim. -/
def batchRounds : E → List (E × E) → Chain (List E × E)
  | claim, [] => return ([], claim)
  | claim, (g1, gInf) :: rest => do
    observe g1
    observe gInf
    let r ← sample
    let g0 := claim + g1
    let (rs, final) ← batchRounds ((gInf * r + (g0 + g1 + gInf)) * r + g0) rest
    return (r :: rs, final)

/-- What a node knows of one child: the child's public input, the claim its proof makes, and
the claim its statement defers. -/
structure ChildClaims where
  /-- The child's public input. -/
  publicInput : Digest
  /-- What its proof claims. -/
  fresh : FixedClaims
  /-- What its statement defers. -/
  carried : DeferredClaim

/-- The words the batching absorbs of a child: its public input's two cells, its proof's claim,
the claim its statement defers (`AGG_CHILD_WORDS`, `lean_ethereum.py:342`). -/
def ChildClaims.words (c : ChildClaims) : List E :=
  [(digestScalars c.publicInput).1, (digestScalars c.publicInput).2] ++ fixedCells c.fresh ++
    c.carried.cells

/-- The prover's part of a batching: the sumcheck's rounds and the bytecode's value at its end
(`bc_sumcheck_msgs`, `bc_star_hint`). -/
structure BatchHints where
  /-- The sumcheck's rounds. -/
  bytecodeRounds : List (E × E)
  /-- The bytecode's value at the end. -/
  bytecodeValue : E

/-- The batching transcript's label (`RECURSION_AGG_LABEL`, `aggregation.rs:69`). -/
def batchLabel : List UInt8 := "leanvm/recursion-aggregation/v1".toUTF8.toList

/-- The batching transcript's initial state (`FiatShamirState::from_label`): Keccak-f of the
label's hash in lanes `0..4`, the other lanes zero. The guest bakes its capacity (`AGG_SEED_*`,
`aggregation.rs:2618-2621`). -/
def batchSeed : KState := keccakF (seedInput (keccak256 batchLabel) (Vector.replicate 4 0))

/-- **The batching**: one transcript absorbs the children's count, then every child's public
input and claims, each group padded to a whole rate; it squeezes two coefficients per child,
and one sumcheck reduces every child's two claims on the bytecode to one point. The claim
deferred there, if the sumcheck closes. -/
def batch (children : List ChildClaims) (h : BatchHints) : Option DeferredClaim :=
  go.run' ⟨batchSeed, []⟩
where
  /-- The transcript. -/
  go : Chain (Option DeferredClaim) := do
    for x in padRate [gpow children.length] do observe x
    for c in children do
      for x in padRate c.words do observe x
    let mut lambdas : List (E × E) := []
    for _ in children do
      let lf ← sample
      let lc ← sample
      lambdas := lambdas ++ [(lf, lc)]
    let claim := sumE (List.zipWith (fun c l ↦
      l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) children lambdas)
    let (r, final) ← batchRounds claim h.bytecodeRounds
    let weight := sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.fresh.bytecodePoint r + l.2 * eqEval c.carried.bytecodePoint r)
      children lambdas)
    if final = h.bytecodeValue * weight then return some ⟨r, h.bytecodeValue⟩
    else return none

/-! ## The node -/

/-- A child of a node: its statement, its proof, and what the proof claims of the bytecode. -/
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

/-- What a node holds its statement by: its children, a holder for every claim, and the batching's
hints. -/
structure NodeWitness where
  /-- The children. -/
  children : List Child
  /-- The leanXMSS claims' holders. -/
  xmss : List (Holder LeanXmss.Signature)
  /-- The leanSPHINCS claims' holders. -/
  sphincs : List (Holder Sphincs.Signature)
  /-- The DA claims' holders. -/
  da : List (Holder Da.Witness)
  /-- The batching's hints. -/
  hints : BatchHints

/-- The leanXMSS claim is held: by a signature, at any leaf index, or by a child making it. -/
def XmssHeld (children : List Child) (claim : XmssClaim) : Holder LeanXmss.Signature → Prop
  | .direct σ => xmssVerify claim.1 claim.2 σ = true
  | .child i => ∃ c, children[i]? = some c ∧ claim ∈ c.statement.claims.xmss

/-- The leanSPHINCS claim is held: by a signature, or by a child making it. -/
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
* `s` defers the batching of the children's claims on the bytecode, and a node without children
  the bytecode at zero. -/
def NodeRel (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) : Prop :=
  s.defer.Shaped bytecode ∧
  (∀ c ∈ w.children, c.statement.defer.Shaped bytecode ∧
    verifyDeferred bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true) ∧
  List.Forall₂ (XmssHeld w.children) s.claims.xmss w.xmss ∧
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

/-- The guest's deployed seed: its Fiat-Shamir IV (`fs_seed`,
`crates/leanvm_core/src/cpu/mod.rs:68-80`). -/
abbrev deployedSeed (guest : Program) : Digest := fiatShamirIv (bytecodeWords guest)

/-- **What the outer verifier checks of a statement besides its proof**: every DA claim's vector
digest is its root's, and the deferred claim holds of the guest's bytecode. -/
def OuterChecks (guest : Program) (s : NodeStatement) : Prop :=
  (∀ c ∈ s.claims.da, Da.toBytes c.2 = Da.vectorDigestOf c.1) ∧ s.defer.Holds (bytecodeWords guest)

/-- **The outer verifier** of an aggregate of the guest `guest` (`EthereumProof::verify`,
`aggregation.rs:695-717`): every DA claim's vector digest is its root's, the deferred claim holds,
and the proof verifies on the statement's digest under the guest's IV. It omits the deployed
verifier's checks on the lists' form (`check_signer_set`, `check_da_roots`,
`aggregation.rs:541-559`: each list sorted without repeats, fewer than `2^16` signature claims
and at most `16` DA roots), so it accepts more. -/
def verifyAggregate (guest : Program) (s : NodeStatement) (π : Proof) : Prop :=
  OuterChecks guest s ∧
    Verifier.verify (bytecodeWords guest) (statementDigest (deployedSeed guest) s) π = true

end
end LeanVM.Node
