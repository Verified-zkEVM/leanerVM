module

public import Statement.LeanVm
public import Statement.LeanXmss
public import Statement.LeanSphincs
public import Statement.LeanDa
public import Statement.Data.Bytecode
public import Statement.Fast.Schemes

/-!
# The leanISA guest program: aggregation

The specification of a node of the aggregation (its statement, witness and relation `NodeRel`:
leanXMSS and leanSPHINCS claims, a DA digest, children verified by the leanVM verifier with deferred
claims), what a proof of the leanISA guest program establishes with its witness named
(`GuestKnowledge`) and the binding of a statement's digest (`DigestBinds`), the deployed leanISA
guest program (`LeanVM.Guest.guest`, assembled from the generated `Statement/Data/`), its
completeness on the covered nodes (`GuestCompleteCovered`, with the deployed limits it assumes) and on its own honest proofs as children (`GuestChildComplete`), and the recursion
step, the batching of the children's deferred claims, sound in the random-permutation model
(`BatchSound`).

Transcribed from leanVM at the pin (`../leanvm-rev`), `crates/rec_aggregation/src/aggregation.rs`
(the statement, its digest, the batching, the outer verifier) and
`crates/rec_aggregation/guests/lean_ethereum.py` (the guest program); `aggregation.rs:N`,
`lean_ethereum.py:N` and `G:N` (the same file) are lines of those files at the pin. The signature
schemes are those whose security `lean_xmss` and `lean_sphincs` prove (`LeanXmss.lean`,
`LeanSphincs.lean`), with Keccak-256 as their hash; LeanDA is `LeanDa.lean`'s, whose security
`lean_da` proves.

A node's statement is a list of signature claims, a DA digest, and a claim on the polynomial
that the protocol fixes, the guest program's stacked bytecode, which the node defers rather than
evaluates (`NodeStatement`). Its public input is the statement's digest under a seed, the guest
program's Fiat-Shamir IV (`statementDigest`). A node holds every signature claim either directly,
by a leanXMSS or leanSPHINCS signature, or through a child that makes the same claim; its DA digest
is that of the blob matrix it checks, zeros, or a child's.
A child is a statement under the same seed and a proof that the deferring verifier accepts for it
(`LeanVM.Protocol.Verifier.verifyDeferred`, the guest program's `verify_sub`), which reads only the
bytecode's length: the bytecode's value at the child's point is taken from the witness (`fresh`)
and checked only at the root, in the batched claim. The node batches the
claims that its children's proofs make of the bytecode, with those its children's statements defer,
into its own deferred claim (`Batch.batchOf`).

What a valid execution of the leanISA guest program establishes is `NodeRel` of the witness its
memory holds, on Keccak as the guest program computes it: the witness is the knowledge content,
since "some signature verifies" says little (some signature verifies for almost every key and
message). The soundness statements take the decoder that reads the witness as a parameter: the end
theorems name `LeanVM.Guest.End.decode` (`lean_vm`), which reads every component off the memory and
chooses nothing; they hold of any decoder that outputs valid witnesses, and their content is in the
decoder they name: one that chose another statement of the same digest would satisfy
`AggregateSound` (`Corollaries.lean`) through a Keccak-256 collision. That the root's statement makes every claim held at the leaves is not proved:
it would need Keccak, computed inside the guest program, to behave as Keccak-256 and Keccak-f[1600]
built from the random permutation of `LeanVM.KnowledgeSoundness`.
-/

@[expose] public section

open scoped ENNReal

/-! ## The DA claim

LeanDA's deployed algorithms (`LeanDa.commitCodewords`, `LeanDa.vectorDigest`) are `LeanDa.lean`'s
(`crates/lean_da`, `crates/verifier/src/da.rs`), generic in the hash; here the hash is Keccak-256
(`keccak`), its digest read as LeanDA's 32 bytes (`Digest.toBytes`).

A DA claim (`DaClaim`) is held by a matrix committed to its root whose rows are orthogonal to a
vector of its vector digest; a statement carries the claim's digest (`daClaimDigest`), or zeros (`Witness.Opens`: the guest program's `da_verify`,
`lean_ethereum.py:3920-4058`; the digest two-level, `LeanDa.vectorDigest`, `da_vector_cell`,
`lean_ethereum.py:4048-4058`). Only where the vector is the root's membership vector, as the deployed
outer verifier requires (no end statement here assumes it), are the rows codewords, except with the
membership test's error (`lean_da`'s `membershipVector_eq_dual`, `checker_sound`) and up to a
collision of the vector digest, which is not among `collisionCandidates`; the link to `lean_da`'s
code binding is not proved. The prover's copy of the membership vector
(`crates/lean_da/src/membership.rs`) is not transcribed.
-/

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- Keccak-256 as LeanDA's hash: the digest's 32 bytes (`Digest.toBytes`). -/
def keccak (input : List UInt8) : Common.KDigest := (keccak256 input).toBytes

/-- What holds a DA claim: a matrix of codewords and the vector its rows are orthogonal to. -/
structure Witness where
  rows : List (List K)
  vector : List E

/-- **The witness holds the DA claim `⟨root, vd⟩`** (`da_verify`): `1` to `1024` codewords of
`2^15` symbols commit to `root`, and every one is orthogonal to the vector, whose digest is
`vd`. -/
def Witness.Opens (root vd : Digest) (w : Witness) : Prop :=
  1 ≤ w.rows.length ∧ w.rows.length ≤ LeanDa.maxRows ∧
    (∀ row ∈ w.rows, row.length = 2 ^ LeanDa.logM) ∧
    LeanDa.commitCodewords keccak w.rows = root.toBytes ∧ w.vector.length = 2 ^ LeanDa.logM ∧
    LeanDa.vectorDigest keccak w.vector = vd.toBytes ∧
    ∀ row ∈ w.rows, LeanDa.dot (fun b ↦ w.vector.getD b 0) (fun b ↦ row.getD b 0) = 0

end LeanVM.Da

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

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
(`LeanXmssClaim`, `aggregation.rs:63`). -/
abbrev XmssClaim : Type := LeanXmss.PublicKey × LeanXmss.Message

/-- A leanSPHINCS key and a message it signed (`LeanSphincsClaim`, `aggregation.rs:66`). -/
abbrev SphincsClaim : Type := Sphincs.PublicKey × Sphincs.Message

/-- **A DA claim**: a blob matrix's Merkle root (an aggregate's `da_root`, `aggregation.rs:392-394`)
with the digest of the vector its rows are orthogonal to. A statement carries its digest,
`daClaimDigest`: the root then the vector digest, hashed (`root_vector_digest`,
`aggregation.rs:559-562`; the guest program's `keccak([root_0, root_1], [vector_0, vector_1])`,
`lean_ethereum.py:4169`). -/
structure DaClaim where
  /-- The matrix's Merkle root: the commitment to its codewords (`Da.Witness.Opens`). -/
  daRoot : Digest
  /-- The digest of the vector, which the guest program takes from `da_verify`'s run; the deployed
  outer verifier derives it as `vector_digest(membership_vector(root))` (`da_digest`,
  `aggregation.rs:553-557`; `crates/verifier/src/da.rs:98-103`). -/
  membershipVectorDigest : Digest
  deriving DecidableEq, Inhabited

/-- A node's claims: leanXMSS claims, leanSPHINCS claims, and its DA digest: a DA claim's
`daClaimDigest`, or `zeroDigest` without one (`da_digest`, `aggregation.rs:550-557`). -/
structure Claims where
  xmss : List XmssClaim
  sphincs : List SphincsClaim
  da : Digest

/-- The claim the statement defers on the stacked bytecode: its value at a point
(`DeferredClaim`, `aggregation.rs:242-245`), the shape of a proof's claim (`FixedClaims`). -/
abbrev DeferredClaim : Type := FixedClaims

/-- A node's statement: its claims and its deferred claim. -/
structure NodeStatement where
  claims : Claims
  defer : DeferredClaim

/-- The deferred claim has the shape of the bytecode `bytecode`: a point of `log₂` of its length
(`bytecode_vars`, `aggregation.rs:795-797`; `BYTECODE_VARS`, `lean_ethereum.py:330`). -/
def DeferredClaim.Shaped (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.bytecodePoint.length = Nat.log2 bytecode.length

/-- **The deferred claim is true** of the bytecode `bytecode`: it has the shape, and the value is
the bytecode's multilinear extension at the point (`DeferredClaim::recompute_scalar`,
`aggregation.rs:263-295`). The length being `2 ^ len` is part of it: `Shaped` reads `Nat.log2` of
the length, which a bytecode of other length shares, and the extension is of `2 ^ len` values. -/
def DeferredClaim.Holds (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.Shaped bytecode ∧ 2 ^ c.bytecodePoint.length = bytecode.length ∧
    multilinearEval (bytecode.map ofK) c.bytecodePoint = c.bytecodeValue

/-- What a leaf defers: the bytecode at the all-zero point (`DeferredClaim::leaf`,
`aggregation.rs:250-252`; `main`'s leaf branch, `lean_ethereum.py:4215-4223`). The value is
the outer verifier's to check. -/
def DeferredClaim.AtZero (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.bytecodePoint = List.replicate (Nat.log2 bytecode.length) 0

/-- The cells a deferred claim is hashed and absorbed as, and a proof's claim on the bytecode
exported as: the point, then the value (`DeferredClaim::cells`, `aggregation.rs:297-301`; the guest
program's `defer_stmt`, and `verify_sub`'s `defer_out`, `lean_ethereum.py:3329-3334`, the point
being the bus point's row coordinates, then the selector challenges). -/
def DeferredClaim.cells (c : DeferredClaim) : List E :=
  c.bytecodePoint ++ [c.bytecodeValue]

/-! ## The statement's digest

Each digest is Keccak-256 of its preimage; the preimages are also the inputs of the candidate
collisions (`collisionCandidates`). -/

/-- The 16 bytes of a 128-bit value, least significant byte first: a cell's two limbs. -/
def bytes16 (value : BitVec 128) : List UInt8 := LeanXmss.bytesLE 16 value

/-- A claim as the `64` bytes its list hashes: the key's root and parameter, then the message
(`claim_cells`, `aggregation.rs:217-224`). -/
def claimBytes (root parameter : BitVec 128) (message : BitVec 256) : List UInt8 :=
  bytes16 root ++ bytes16 parameter ++ LeanXmss.bytesLE 32 message

/-- The bytes `claimListDigest claims` hashes. Both schemes' keys are a root and a parameter
(`XmssClaim` and `SphincsClaim` are one type). -/
def claimsPreimage (claims : List XmssClaim) : List UInt8 :=
  claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2

/-- The digest of a list of leanXMSS or leanSPHINCS claims (`claim_list_digest`,
`aggregation.rs:211-213`, `lean_ethereum.py:3827-3849`). -/
def claimListDigest (claims : List XmssClaim) : Digest := keccak256 (claimsPreimage claims)

/-- The bytes `daClaimDigest c` hashes: the root, then the vector digest. -/
def daPreimage (c : DaClaim) : List UInt8 :=
  digestBytes c.daRoot ++ digestBytes c.membershipVectorDigest

/-- A DA claim's digest, which a statement carries (`root_vector_digest`, `aggregation.rs:559-562`;
`lean_ethereum.py:4169`). -/
def daClaimDigest (c : DaClaim) : Digest := keccak256 (daPreimage c)

/-- The DA digest of a statement without a DA claim: zeros (`da_digest(None)`,
`aggregation.rs:553-557`; `own_da`'s zero cells, `lean_ethereum.py:4171-4172`). -/
def zeroDigest : Digest := Vector.replicate 4 0

/-- The 24 bytes of a field element, its three limbs. -/
def eBytes (x : E) : List UInt8 := kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2)

/-- The deferred claim's cells, an odd count paired with a zero cell. -/
def paddedCells (c : DeferredClaim) : List E :=
  c.cells ++ if c.cells.length % 2 = 1 then [0] else []

/-- The bytes `statementDigest seed s` hashes: the seed, the leanXMSS and leanSPHINCS claims'
digests, the DA digest, then the padded deferred cells. Each list's digest binds its length
through Keccak's padding. -/
def statementPreimage (seed : Digest) (s : NodeStatement) : List UInt8 :=
  digestBytes seed ++ digestBytes (claimListDigest s.claims.xmss) ++
    digestBytes (claimListDigest s.claims.sphincs) ++ digestBytes s.claims.da ++
    (paddedCells s.defer).flatMap eBytes

/-- **The statement's digest under `seed`** (`statement_digest`, `aggregation.rs:331-360`,
`lean_ethereum.py:3764-3795`). The cells carry no lengths: the digest tells two deferred claims
apart only at one shape. -/
def statementDigest (seed : Digest) (s : NodeStatement) : Digest :=
  keccak256 (statementPreimage seed s)

/-! ## Batching the deferred claims (`aggregate_claims`, `lean_ethereum.py:4234-4341`;
`aggregate_deferred_claims`, `aggregation.rs:910-1012`) -/

/-- Words padded with zeros to a whole rate, `rateScalars` words (`pad`,
`aggregation.rs:920-924`; `AGG_CHILD_PAD`). -/
def padRate (words : List E) : List E :=
  words ++ List.replicate ((rateScalars - words.length % rateScalars) % rateScalars) 0

/-- What a node knows of one child: the child's public input, the claim its proof makes
(`fresh`), and the claim its statement defers (`carried`). -/
structure ChildClaims where
  publicInput : Digest
  fresh : FixedClaims
  carried : DeferredClaim

/-- The words the batching absorbs of a child: its public input's two cells, its proof's claim,
the claim its statement defers (`AGG_CHILD_WORDS`, `lean_ethereum.py:342`). -/
def ChildClaims.words (c : ChildClaims) : List E :=
  [(digestScalars c.publicInput).1, (digestScalars c.publicInput).2] ++ DeferredClaim.cells c.fresh ++
    c.carried.cells

/-- The bytecode's batched claim at the lambdas `lB`. -/
def _root_.LeanVM.Guest.Batch.claimBOf (cs : List ChildClaims) (lB : List (E × E)) : E :=
  sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) cs lB)

/-- The bytecode's batched weight at `y`. -/
def _root_.LeanVM.Guest.Batch.bytecodeWeight (cs : List ChildClaims) (lB : List (E × E))
    (y : List E) : E :=
  sumE (List.zipWith (fun c l ↦
    l.1 * eqEval c.fresh.bytecodePoint y + l.2 * eqEval c.carried.bytecodePoint y) cs lB)

/-- **The round polynomial** from the claim before the round and its message `(g(1), g(∞))`:
`g(0) = claim + g(1)`, and `g(x) = (g(∞)·x + g(0) + g(1) + g(∞))·x + g(0)`, the degree-2 round
polynomial whose `g(0)` the claim fixes. -/
def _root_.LeanVM.Guest.Batch.roundPoly (claim : E) (g : E × E) (x : E) : E :=
  (g.2 * x + ((claim + g.1) + g.1 + g.2)) * x + (claim + g.1)

/-- The prover's part of a batching: the sumcheck's rounds and the bytecode's value at its end
(`bc_sumcheck_msgs`, `bc_star_hint`). -/
structure BatchHints where
  bytecodeRounds : List (E × E)
  bytecodeValue : E

/-- The batching transcript's label (`RECURSION_AGG_LABEL`, `aggregation.rs:72`). -/
def batchLabel : List UInt8 := "leanvm/recursion-aggregation/v1".toUTF8.toList

end LeanVM.Node

/-! The batching as a program of the verifier's language (`Prog`): the count `n` as `g^n` then
three zeros, `n` children of `bytecode`'s shapes, each its words then zeros to a whole rate
(`readChildren`), then the lambdas, the sumcheck's `log₂ |bytecode|` rounds (`roundsProg`) and
the final value, accepted if the final claim is the value times the batched weight and the
deferred claim meets a check (`batchRest`); run from the batching transcript's seed
(`batchRun`). A node's batching (`NodeRel`) runs `batchOf`, the check that the claim is the node's;
the recursion step's end statement (`BatchSound`) runs `batchAny`, the count read below a bound
and the check that the claim holds of `bytecode`. -/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

/-- The words of a child at `nB` bytecode coordinates: its public input's two, its proof's
claim, its statement's claim. -/
def childLen (nB : ℕ) : ℕ := 2 + (nB + 1) + (nB + 1)

/-- The zeros that pad `k` words to a whole rate. -/
def padLen (k : ℕ) : ℕ := (rateScalars - k % rateScalars) % rateScalars

/-- A child read off its words (`ChildClaims.words`), at `nB` bytecode coordinates; `none` where
the public input does not decode. -/
def parseChild (nB : ℕ) (xs : List E) : Option ChildClaims := do
  let pi ← digestOfScalars (xs.getD 0 0, xs.getD 1 0)
  let ys := xs.drop 2
  let zs := ys.drop (nB + 1)
  return ⟨pi, ⟨ys.take nB, ys.getD nB 0⟩, ⟨zs.take nB, zs.getD nB 0⟩⟩

/-- A child has the bytecode's shapes: its proof's claim and its statement's are at points of
`log₂` of the bytecode's length. -/
def ChildShaped (bytecode : List K) (c : ChildClaims) : Prop :=
  c.fresh.bytecodePoint.length = Nat.log2 bytecode.length ∧ c.carried.Shaped bytecode

/-- Read a child: its words, then the zeros to a whole rate. -/
def readChild (nB : ℕ) : Prog ChildClaims := do
  let xs ← Prog.readN (childLen nB + padLen (childLen nB))
  Prog.require (xs.drop (childLen nB) = List.replicate (padLen (childLen nB)) 0)
  liftOption (parseChild nB xs)

/-- Read `n` children. -/
def readChildren (nB : ℕ) : ℕ → Prog (List ChildClaims)
  | 0 => pure []
  | n + 1 => do
    let c ← readChild nB
    let cs ← readChildren nB n
    return c :: cs

open Classical in
/-- The count below `M` whose power of the generator is `x`, if any. -/
noncomputable def countOf (M : ℕ) (x : E) : Option ℕ :=
  if h : ∃ n, n < M ∧ Verifier.gpow n = x then some (Nat.find h) else none

/-- Read the count: `g^n`, then three zeros. -/
noncomputable def readCount (M : ℕ) : Prog ℕ := do
  let xs ← Prog.readN rateScalars
  Prog.require (xs.drop 1 = List.replicate (rateScalars - 1) 0)
  liftOption (countOf M (xs.getD 0 0))

/-- Sample a pair of lambdas per child. -/
def sampleL : ℕ → Prog (List (E × E))
  | 0 => pure []
  | n + 1 => do
    let a ← Prog.sampleE
    let b ← Prog.sampleE
    let l ← sampleL n
    return (a, b) :: l

/-- `k` rounds of the batching sumcheck from `claim`: read `g(1)` and `g(∞)`, sample the
challenge, fold (`roundPoly`). The challenges and the final claim. -/
def roundsProg : E → ℕ → Prog (List E × E)
  | claim, 0 => pure ([], claim)
  | claim, k + 1 => do
    let g1 ← Prog.readE
    let gInf ← Prog.readE
    let r ← Prog.sampleE
    let rest ← roundsProg (roundPoly claim (g1, gInf) r) k
    return (r :: rest.1, rest.2)

open Classical in
/-- **The batching after its children**: the lambdas, the sumcheck's `log₂ |bytecode|` rounds,
the final value (`bc_star_hint`, read after the last challenge: no challenge follows), the final
check, and `check` of the deferred claim. -/
noncomputable def batchRest (check : DeferredClaim → Prop) (bytecode : List K)
    (cs : List ChildClaims) : Prog Bool := do
  let l ← sampleL cs.length
  let rb ← roundsProg (claimBOf cs l) (Nat.log2 bytecode.length)
  let bv ← Prog.readE
  Prog.require (rb.2 = bv * bytecodeWeight cs l rb.1 ∧ check ⟨rb.1, bv⟩)
  return true

/-- **The batching of `n` children.** -/
noncomputable def batchProg (check : DeferredClaim → Prop) (bytecode : List K) (n : ℕ) :
    Prog Bool := do
  let cs ← readChildren (Nat.log2 bytecode.length) n
  batchRest check bytecode cs

/-- The count's cells: the generator's power, padded to a whole rate. -/
def headCells (n : ℕ) : List E := padRate [Verifier.gpow n]

/-- A child's cells: its words, padded to a whole rate. -/
def childCells (c : ChildClaims) : List E := padRate c.words

/-- What the batching absorbs before its first challenge. -/
def batchWords (cs : List ChildClaims) : List E := headCells cs.length ++ cs.flatMap childCells

/-- **The batching of a node's `n` children** (`aggregate_claims`): the count's cells, then the
batching of `n`, its deferred claim meeting `check`. -/
noncomputable def batchOf (check : DeferredClaim → Prop) (bytecode : List K) (n : ℕ) :
    Prog Bool := do
  let xs ← Prog.readN rateScalars
  Prog.require (xs = headCells n)
  batchProg check bytecode n

/-- **The batching as a verifier program**, of fewer than `M` children: the count, then the
batching of that many, its deferred claim true of `bytecode`. -/
noncomputable def batchAny (M : ℕ) (bytecode : List K) : Prog Bool := do
  let n ← readCount M
  batchProg (DeferredClaim.Holds bytecode) bytecode n

/-- **The batching transcript run**, for a hash function `H` and a permutation `F` in any monad:
from the seed `F(H(label) ‖ 0)` (`FiatShamirState::from_label`; the guest program bakes its
capacity, `AGG_SEED_*`, `aggregation.rs:2507-2510`), the program on the proof. -/
noncomputable def batchRun {m : Type → Type} [Monad m] (H : Bytes → m Digest)
    (F : KState → m KState) (prog : Prog Bool) (proof : Proof) : m Bool := do
  let seed ← F (seedInput (← H batchLabel) (Vector.replicate 4 0))
  runProof H F prog seed proof

/-- The stream of a node's batching: the count's and the children's cells, the sumcheck's
messages `(g(1), g(∞))`, the final value. -/
def batchStream (cs : List ChildClaims) (h : BatchHints) : List E :=
  batchWords cs ++ h.bytecodeRounds.flatMap (fun g ↦ [g.1, g.2]) ++ [h.bytecodeValue]

end LeanVM.Guest.Batch

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The node -/

/-- A child of a node: its statement, its proof, and what the proof claims of the bytecode. -/
structure Child where
  statement : NodeStatement
  fresh : FixedClaims
  proof : Proof

/-- How a node holds a claim: directly, by a witness, or through its `i`-th child. -/
inductive Holder (W : Type) where
  | direct (w : W)
  | child (i : ℕ)

/-- What a node holds its statement by: its children, a holder for every signature claim, the blob
matrix it checks directly with the DA claim it opens (if any), and the batching's hints. -/
structure NodeWitness where
  children : List Child
  xmss : List (Holder LeanXmss.Signature)
  sphincs : List (Holder Sphincs.Signature)
  da : Option (DaClaim × Da.Witness)
  hints : BatchHints

/-- **A claim is held**: by a witness `w` that `holds`, or by a child whose claims of the kind
(`claimsOf`) make it. -/
def Held {α W : Type} (holds : α → W → Prop) (claimsOf : Claims → List α) (children : List Child)
    (claim : α) : Holder W → Prop
  | .direct w => holds claim w
  | .child i => ∃ c, children[i]? = some c ∧ claim ∈ claimsOf c.statement.claims

/-- **What the witness `w` establishes of a node's statement `s`**, for the guest program's bytecode
`bytecode` and under the seed `seed`:
* every deferred claim, the node's and its children's, has the bytecode's shape;
* the deferring verifier accepts every child's proof, for the child's statement under the same
  seed, the bytecode's value at the child's point taken from the witness (`fresh`; checked only at
  the root, in the batched claim);
* every signature claim of `s` is held;
* its DA digest is that of the claim the matrix it checks opens, or, without one, zero or a
  child's DA digest (`da_pick`, `lean_ethereum.py:4207-4211`);
* `s` defers the batching of the children's claims on the bytecode (`batchOf`, on the stream of
  the children's claims and the hints), and a node without children the bytecode at zero. -/
def NodeRel (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) : Prop :=
  s.defer.Shaped bytecode ∧
  (∀ c ∈ w.children, c.statement.defer.Shaped bytecode ∧
    verifyDeferred bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true) ∧
  -- a leanXMSS claim by a signature at any leaf index, a leanSPHINCS claim by a signature
  List.Forall₂ (Held (fun (c : XmssClaim) σ ↦ xmssVerify c.1 c.2 σ = true) Claims.xmss
    w.children) s.claims.xmss w.xmss ∧
  List.Forall₂ (Held (fun (c : SphincsClaim) σ ↦ sphincsVerify c.1 c.2 σ = true) Claims.sphincs
    w.children) s.claims.sphincs w.sphincs ∧
  -- the DA digest: the claim the matrix checked directly opens, else zero or a child's
  (match w.da with
    | some (c, m) => s.claims.da = daClaimDigest c ∧ m.Opens c.daRoot c.membershipVectorDigest
    | none => s.claims.da = zeroDigest ∨ ∃ c ∈ w.children, c.statement.claims.da = s.claims.da) ∧
  if w.children = [] then s.defer.AtZero bytecode
  else Guest.Batch.batchRun (m := Id) keccak256 keccakF
    (Guest.Batch.batchOf (· = s.defer) bytecode w.children.length)
    ⟨Guest.Batch.batchStream (w.children.map fun c ↦
      ⟨statementDigest seed c.statement, c.fresh, c.statement.defer⟩) w.hints, []⟩ = true

/-- The guest program's deployed seed: its Fiat-Shamir IV (`fs_seed`,
`crates/leanvm_core/src/cpu/mod.rs:63-67`). -/
abbrev deployedSeed (guest : Program) : Digest := fiatShamirIv (bytecodeWords guest)

/-! ## What a proof of the leanISA guest program establishes, its witness named -/

/-- **The candidate collisions** of two statements' digests: the pairs of inputs of the three
hashes the digests compute, the outer one and the two claim lists'. The DA digest enters the
preimage as it is. -/
def collisionCandidates (seed : Digest) (s : NodeStatement) (seed' : Digest)
    (s' : NodeStatement) : List (List UInt8 × List UInt8) :=
  [(statementPreimage seed s, statementPreimage seed' s'),
    (claimsPreimage s.claims.xmss, claimsPreimage s'.claims.xmss),
    (claimsPreimage s.claims.sphincs, claimsPreimage s'.claims.sphincs)]

/-- **A collision**: a pair of different inputs with the same Keccak-256 digest, among
`pairs`. -/
def HasCollision (pairs : List (List UInt8 × List UInt8)) : Prop :=
  ∃ p ∈ pairs, p.1 ≠ p.2 ∧ keccak256 p.1 = keccak256 p.2

/-- **The statement's digest binds the seed and the statement**: two statements whose deferred
claims have the shape of one bytecode and whose digests (under two seeds) are equal are the same
statement under the same seed, or one of the candidate pairs is a Keccak-256 collision. The shape
fixes the length of the deferred claim's point, which the digest does not record. Proved by
`LeanVM.Guest.Binding.digest_binds`. -/
def DigestBinds : Prop :=
  ∀ (b : List K) (seed seed' : Digest) (s s' : NodeStatement),
    s.defer.Shaped b → s'.defer.Shaped b → statementDigest seed s = statementDigest seed' s' →
      (seed = seed' ∧ s = s') ∨ HasCollision (collisionCandidates seed s seed' s')

/-- What a decoder reads off a memory: a seed, a statement and a witness. -/
structure Decoded where
  seed : Digest
  statement : NodeStatement
  witness : NodeWitness

/-- A decoder: from a memory, a seed, a statement and a witness. -/
abbrev Decoder : Type := ∀ {κ : ℕ}, MemImage κ → Decoded

/-- **What a valid execution of `guest` on `input` contains**, as `d` reads it off the memory: a
seed and a node statement whose digest under that seed is the input's digest (the statement the
input commits to), and a witness proving that statement (`NodeRel`: each of its claims is held, by
a signature, a blob or a child whose proof the deferring verifier accepts, and its deferred claim is
the batching of its children's). -/
def DecodesOn (guest : Program) (input : PublicInput) (d : Decoded) : Prop :=
  statementDigest d.seed d.statement = publicDigest input ∧
    NodeRel (bytecodeWords guest) d.seed d.statement d.witness

/-- **Knowledge soundness of the leanISA guest program, its witness named**: from the memory of
every valid execution of `guest` on a public input, `decode` reads a seed, the node statement the
input commits to under that seed, and a witness proving it (`DecodesOn`). -/
def GuestKnowledge (guest : Program) (decode : Decoder) : Prop :=
  ∀ input (t : Trace guest), ValidExecution guest input t → DecodesOn guest input (decode t.image)

end LeanVM.Node

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

/-! ## The deployed leanISA guest program -/

/-- The leanISA guest program's bytecode. -/
def guest : Program := assemble Data.functions 19 (by decide)

/-! ## Coverage slots (read by `Limits`, `Covered`) -/

namespace Hints

/-- `STREAM_CAP` (`aggregation.rs:1326`): a child's proof stream is zero-padded to it. -/
def streamCap : ℕ := 8192

/-- `MU_MIN` (`aggregation.rs:1317`): the least stack log the guest program has an opening arm
for. -/
def muMin : ℕ := 22

/-- A claim takes its declared slot if it is free, else the next duplicate slot (`take_slot`).
The state is which declared slots are taken, and the duplicates so far. -/
def takeSlot {α : Type} [BEq α] (declared : List α) (st : List Bool × List α) (claim : α) :
    ℕ × (List Bool × List α) :=
  match (List.range declared.length).find? fun j ↦
      declared[j]? == some claim && !(st.1.getD j true) with
  | some j => (j, (st.1.set j true, st.2))
  | none => (declared.length + st.2.length, (st.1, st.2 ++ [claim]))

/-- The slots of claims taken in order. -/
def takeSlots {α : Type} [BEq α] (declared : List α) :
    List Bool × List α → List α → List ℕ × (List Bool × List α)
  | st, [] => ([], st)
  | st, c :: cs =>
    let (i, st) := takeSlot declared st c
    let (is, st) := takeSlots declared st cs
    (i :: is, st)

/-- The slots of lists of claims taken in order. -/
def takeSlotsAll {α : Type} [BEq α] (declared : List α) :
    List Bool × List α → List (List α) → List (List ℕ) × (List Bool × List α)
  | st, [] => ([], st)
  | st, c :: cs =>
    let (i, st) := takeSlots declared st c
    let (is, st) := takeSlotsAll declared st cs
    (i :: is, st)

/-- One region of the coverage table: its duplicate claims, in slot order, and the slot of every
raw claim and of every child's claims. -/
structure Region (α : Type) where
  dups : List α
  raw : List ℕ
  children : List (List ℕ)

/-- The region of the declared claims: the raw claims take their slots, then the children's. -/
def plan {α : Type} [BEq α] (declared raw : List α) (children : List (List α)) : Region α :=
  let (raw, st) := takeSlots declared (declared.map fun _ ↦ false, []) raw
  let (children, st) := takeSlotsAll declared st children
  ⟨st.2, raw, children⟩

/-- The claims held directly, with their witnesses, in the statement's order. -/
def direct {α W : Type} : List α → List (Holder W) → List (α × W)
  | c :: cs, .direct w :: hs => (c, w) :: direct cs hs
  | _ :: cs, .child _ :: hs => direct cs hs
  | _, _ => []

/-- The deferring verifier's initial state on a child's proof under the node's seed
(`verifyDeferredWith`). -/
def childStart (seed : Digest) (c : Child) : St :=
  ⟨⟨keccakF (seedInput seed (statementDigest seed c.statement)), []⟩, c.proof.stream,
    c.proof.openings, []⟩

end Hints

/-! ## The deployed limits

The guest program divides by some of the verifier's challenges (the WHIR fold and tail challenges
and each level's batching challenge `λ`, G:1251, 1560, 1565), so a zero one makes it reject a child
the verifier accepts; its hypothesis refuses a zero challenge anywhere (`Prog.refuseZero`), a
slightly stronger one, each challenge being zero with probability `2^-192`. -/

/-- **`P` refusing a zero challenge**: every sampled challenge `0` fails. -/
def _root_.LeanVM.Protocol.Compile.Prog.refuseZero {α : Type} : Prog α → Prog α
  | .ret a => .ret a
  | .fail => .fail
  | .read k => .read fun x ↦ (k x).refuseZero
  | .sample k => .sample fun x ↦ if x = 0 then .fail else (k x).refuseZero
  | .grind bits k => .grind bits k.refuseZero
  | .commit height width k => .commit height width k.refuseZero
  | .query i ps k => .query i ps fun rows ↦ (k rows).refuseZero

namespace Limits

/-- **The deployed deferring verifier refusing a zero challenge** (`Prog.refuseZero`):
`verifyDeferred` with every sampled challenge `0` a failure. -/
def verifyDeferredRZ (bytecode : List K) (iv publicInput : Digest) (c : FixedClaims)
    (π : Proof) : Bool :=
  Id.run (runProof (m := Id) keccak256 keccakF (deferredProgram c bytecode publicInput).refuseZero
    (keccakF (seedInput iv publicInput)) π)

/-- **The query steps of a run** of the compiled verifier (Keccak-256, Keccak-f[1600]): each
`query` step as its tree's height and its positions, each with the opening it consumes. -/
def queriesOf {α : Type} : Prog α → St → List (ℕ × List (ℕ × Opening))
  | .ret _, _ => []
  | .fail, _ => []
  | .read k, s => match s.stream with
    | [] => []
    | x :: xs =>
      queriesOf (k x) { s with sponge := Id.run (absorb keccakF s.sponge x dsObserve), stream := xs }
  | .sample k, s =>
    let (c, sp) := Id.run (squeeze keccakF s.sponge)
    queriesOf (k c) { s with sponge := sp }
  | .grind bits k, s => match s.stream with
    | [] => []
    | n :: xs =>
      let (c, sp) := Id.run (squeeze keccakF (Id.run (absorb keccakF s.sponge n dsPowNonce)))
      if powOk bits n c then queriesOf k { s with sponge := sp, stream := xs } else []
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs =>
      match digestOfScalars (x0, x1) with
      | some root =>
        queriesOf k { s with
          sponge := Id.run (absorb keccakF (Id.run (absorb keccakF s.sponge x0 dsObserve)) x1 dsObserve)
          stream := xs
          roots := s.roots ++ [(root, height, width)] }
      | none => []
    | _ => []
  | .query i ps k, s => match s.roots[i]? with
    | none => []
    | some (root, height, width) =>
      match Id.run (openAll (m := Id) keccak256 root height width ps s.openings) with
      | some (rows, rest) =>
        (height, ps.zip s.openings) :: queriesOf (k rows) { s with openings := rest }
      | none => []

/-- The heap index of the node at level `l` (the leaves at `0`) above the leaf `q` of a tree of
height `depth`. -/
def heapNode (depth q l : ℕ) : ℕ := 2 ^ (depth - l) + q / 2 ^ l

/-- The heap index of the sibling of the node at level `l < depth` above the leaf `q`. -/
def sibNode (depth q l : ℕ) : ℕ := 2 * heapNode depth q (l + 1) + (!q.testBit l).toNat

/-- The digest an opening's climb reaches from `node` at position `q` over `path`. -/
def climbTo (node : Digest) (q : ℕ) (path : List Digest) : Digest :=
  Id.run (climb (m := Id) keccak256 node q path)

/-- **The opening `o` at `q` gives the heap node `v` the digest `d`**: `v` is on its climb, with
the climb's digest there, or is the sibling it carries at a level. -/
def NodeIs (depth : ℕ) (a : ℕ × Opening) (v : ℕ) (d : Digest) : Prop :=
  (∃ l ≤ depth, v = heapNode depth a.1 l ∧ d = climbTo (hashWords a.2.leaf) a.1 (a.2.path.take l)) ∨
    ∃ l < depth, v = sibNode depth a.1 l ∧ d = a.2.path.getD l default

/-- The openings of one query step agree wherever they meet. -/
def BatchAgrees (depth : ℕ) (qs : List (ℕ × Opening)) : Prop :=
  ∀ a ∈ qs, ∀ b ∈ qs, ∀ v d d', NodeIs depth a v d → NodeIs depth b v d' → d = d'

end Limits

/-- **A child the guest program accepts** under the seed `seed`: what the guest program asks of
each child, `NodeRel`'s two conditions (`shaped`, `verifies`) and the deployed ones:
* its stack log is at least `MU_MIN = 22`: the guest program has one opening arm per stack log in
  `[22, 28]` (G:3312-3314); the verifier admits stack logs from `Whir.minLogStack`;
* its proof stream is at most `STREAM_CAP = 8192` scalars (G:3163);
* its openings agree in the guest program's Merkle caps: at every query step of its deferring
  verifier, run under the node's seed, the step's openings agree wherever they meet (one tree's
  openings, the honest prover's, agree);
* no zero challenge: its proof is accepted by the deferring verifier refusing a zero challenge
  anywhere (`verifyDeferredRZ`), as the guest program divides by some (above). -/
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
    Limits.verifyDeferredRZ bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true

open Hints in
/-- The coverage table's slots (`n_total`, G:4102): each region's declared claims and its
duplicates, as `plan` assigns them. -/
def coverage (s : NodeStatement) (w : NodeWitness) : ℕ :=
  let ch := w.children
  s.claims.xmss.length + (plan s.claims.xmss ((direct s.claims.xmss w.xmss).map (·.1))
      (ch.map (·.statement.claims.xmss))).dups.length +
    s.claims.sphincs.length + (plan s.claims.sphincs ((direct s.claims.sphincs w.sphincs).map (·.1))
      (ch.map (·.statement.claims.sphincs))).dups.length

open Hints in
/-- **The deployed limits**, where `NodeRel` admits witnesses the guest program cannot run; a
child's own limits are `ChildOk`'s. Implied by these, with `NodeRel` and `ChildOk`, and so not
limits of their own: a child's stack log at most `28` and rate in `[1, 4]` (`readSizes`), at
most one blob matrix checked directly (`NodeWitness.da`, G:4097), every count of `meta` below
`2^16` (G:4090-4095), the bus depth at most `32` (G:1628), the tables' heights at most `28`
(G:2008). -/
structure Limits (s : NodeStatement) (w : NodeWitness) : Prop where
  /-- A claim declared `n` times is held `n` times, by witnesses or by distinct entries of the
  children's lists: each coverage slot is written once (G:3871-3872, 4153-4154, 4158-4159, 4205), where
  `NodeRel` lets two equal claims share one holder. -/
  xmssHeld : ∀ x, s.claims.xmss.count x ≤ ((direct s.claims.xmss w.xmss).map (·.1)).count x +
    (w.children.map fun c ↦ c.statement.claims.xmss.count x).sum
  sphincsHeld : ∀ x, s.claims.sphincs.count x ≤ ((direct s.claims.sphincs w.sphincs).map (·.1)).count x +
    (w.children.map fun c ↦ c.statement.claims.sphincs.count x).sum
  /-- At most `MAX_RECURSIONS = 16` children (G:4096). -/
  children : w.children.length ≤ 16
  /-- Every child's signature list below `2^16` (G:4190-4191). -/
  lists : ∀ c ∈ w.children, c.statement.claims.xmss.length < 2 ^ 16 ∧
    c.statement.claims.sphincs.length < 2 ^ 16
  /-- The coverage table below `2^16` (G:4103). -/
  coverage : coverage s w < 2 ^ 16

/-! ## The leanISA guest program's completeness on the covered nodes -/

namespace Budget

open Hints

/-- **The nodes the deployed budget covers**, eight families by the node's children, raw
signatures (leanXMSS and leanSPHINCS held directly), the rows of the blob matrix checked directly,
and claims (declared, coverage slots, the children's declared claims): a recursion node
of `2048` claims; a leaf of `2048` raw signatures and claims; `8` children and `2^15` claims; `4`
children, `1024` raw signatures and `8192` claims; `4` children, a matrix of `32` rows and `8192`
claims; `2` children, `256` raw signatures, a matrix of `32` rows and `8192` claims; `2` children,
a matrix of `32` rows and `2^14` claims; no child, a matrix of `32` rows and `2^15` claims. -/
def Covered (s : NodeStatement) (w : NodeWitness) : Prop :=
  let n := w.children.length
  let raw := (direct s.claims.xmss w.xmss).length + (direct s.claims.sphincs w.sphincs).length
  let blobs := (w.da.map fun _ ↦ 1).getD 0
  let rows := (w.da.map fun p ↦ p.2.rows.length).getD 0
  let declared := s.claims.xmss.length + s.claims.sphincs.length
  let kids := (w.children.map fun c ↦ c.statement.claims.xmss.length +
    c.statement.claims.sphincs.length).sum
  let claims (b : ℕ) : Prop := declared ≤ b ∧ coverage s w ≤ b ∧ kids ≤ b
  (raw = 0 ∧ blobs = 0 ∧ claims 2048) ∨
  (n = 0 ∧ blobs = 0 ∧ raw ≤ 2048 ∧ declared ≤ 2048 ∧ coverage s w ≤ 2048) ∨
  (n ≤ 8 ∧ raw = 0 ∧ blobs = 0 ∧ claims (2 ^ 15)) ∨
  (n ≤ 4 ∧ raw ≤ 1024 ∧ blobs = 0 ∧ claims 8192) ∨
  (n ≤ 4 ∧ raw = 0 ∧ rows ≤ 32 ∧ claims 8192) ∨
  (n ≤ 2 ∧ raw ≤ 256 ∧ rows ≤ 32 ∧ claims 8192) ∨
  (n ≤ 2 ∧ raw = 0 ∧ rows ≤ 32 ∧ claims (2 ^ 14)) ∨
  (n = 0 ∧ raw = 0 ∧ rows ≤ 32 ∧ declared ≤ 2 ^ 15 ∧ coverage s w ≤ 2 ^ 15)

/-- **Every covered node has a valid execution of the leanISA guest program**: for every seed,
statement `s` and witness `w` with `NodeRel`, within the deployed limits (so at most `16`
children), every child one the guest program accepts (`ChildOk`: at one of its opening arms, its
openings agreeing in the caps, no zero challenge), and `s` and `w` in one of the families
`Covered` lists, there is a valid execution of the leanISA guest program on the statement's digest of
committed size in `[2^22, 2^28]`. Proved by `LeanVM.Guest.Budget.guest_complete_covered`. -/
abbrev GuestCompleteCovered : Prop :=
  ∀ (seed : Digest) (s : NodeStatement) (w : NodeWitness),
    NodeRel (bytecodeWords guest) seed s w → Limits s w →
    (∀ c ∈ w.children, ChildOk (bytecodeWords guest) seed c) → Covered s w →
    ∃ t : Trace guest,
      ValidExecution guest (PublicInput.ofDigest (statementDigest seed s)) t ∧
      2 ^ 22 ≤ t.committedSize ∧ t.committedSize ≤ 2 ^ 28

/-! ### Honest proofs are children the guest program accepts

The statements above assume of each child what `ChildOk` bundles. The guest program checks a child
with the deployed Keccak, so the honest proof is made with it (`atKeccak`); what it can fail by (a
proof of work without a nonce within its fuel, a zero challenge where the guest program divides) is
bounded in the random-permutation model for the same prover and check (`verifierRZ`). -/

/-- **The leanVM verifier refusing a zero challenge** (`Prog.refuseZero`): `verifier H F` with
every sampled challenge `0` a failure. -/
def verifierRZ {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KState → m KState)
    (prog : Program) (input : PublicInput) (proof : Proof) : m Bool := do
  let seed ← seedWith H F (bytecodeWords prog) (publicDigest input)
  runProof H F (leanVmProgram (bytecodeWords prog) (publicDigest input)).refuseZero seed proof

/-- Keccak-256 and Keccak-f[1600] answering the calls `HashSpec`. -/
def keccakImpl : QueryImpl HashSpec Id
  | .inl x => keccak256 x
  | .inr s => keccakF s

open OracleComp in
/-- **An honest prover's proof with the deployed Keccak-256 and Keccak-f[1600].** -/
def atKeccak (prover : HonestProver) (prog : Program) (input : PublicInput)
    (t : Trace prog) (ρ fuel : ℕ) : Proof :=
  Id.run (simulateQ keccakImpl (prover prog input t ρ fuel))

open OracleComp OracleSpec in
/-- **The honest proof of an execution of the guest program is a child the guest program accepts**:
for the honest prover `LeanVM.prover` (`LeanVm.lean`, `LeanVM.Prover.prove` with the oracle calls),
1. in the random-permutation model, at `2^25` nonces per proof of work, `verifierRZ` rejects its
   proof of a valid execution of committed size at most `2^28`, at an inverse rate `2^ρ`,
   `1 ≤ ρ ≤ 4`, with probability at most `2^-126`;
2. its proof with the deployed Keccak (`atKeccak`) of an execution of the leanISA guest program of
   committed size at least `2^22` on a statement's digest under the deployed seed, wherever
   `verifierRZ` with the deployed Keccak accepts it, forms with the statement (its deferred claim
   shaped) and some claim `fresh` on the bytecode a child the guest program accepts (`ChildOk`).
Reading part 1 for the deployed Keccak, so that part 2 applies to the honest proof, is the
heuristic that the deployed Keccak-f[1600] behaves as a random permutation, applied to this
prover.
Proved by `LeanVM.Guest.Budget.guest_child_complete`. -/
def GuestChildComplete : Prop :=
  (∀ (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ),
    ValidExecution prog input t → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← (simulateQ LeanVM.rpmImpl (do
        let proof ← LeanVM.prover prog input t ρ (2 ^ 25)
        verifierRZ queryH queryF prog input proof)).run' []}[v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 126) ∧
  ∀ (s : NodeStatement) (t : Trace guest) (ρ : ℕ), 2 ^ 22 ≤ t.committedSize →
    s.defer.Shaped (bytecodeWords guest) →
    let input := PublicInput.ofDigest (statementDigest (deployedSeed guest) s)
    let proof := atKeccak LeanVM.prover guest input t ρ (2 ^ 25)
    verifierRZ (m := Id) keccak256 keccakF guest input proof = true →
    ∃ fresh, ChildOk (bytecodeWords guest) (deployedSeed guest) ⟨s, fresh, proof⟩

end Budget

/-! ## The recursion step: the batching in the random-permutation model

The experiment is `rpmRun` (`LeanVm.lean`), the adversary's output with the unit statement (the
batching has no statement of its own). -/

namespace Batch

/-- The proof's stream begins with the count's and the cells of fewer than `M` children of the
bytecode's shapes, one of whose claims is false. -/
def FalseChildren (bytecode : List K) (M : ℕ) (π : Proof) : Prop :=
  ∃ cs : List ChildClaims, cs.length < M ∧ (∀ c ∈ cs, ChildShaped bytecode c) ∧
    batchWords cs <+: π.stream ∧
    ¬ ∀ c ∈ cs, c.fresh.Holds bytecode ∧ c.carried.Holds bytecode

/-- **The batching program's query bound** on child counts below `M`: the seed's two queries,
then a quarter of the program's cost. -/
def batchQueryBound (bytecode : List K) (M : ℕ) : ℕ :=
  2 + (rateScalars + (M * (childLen (Nat.log2 bytecode.length) +
    padLen (childLen (Nat.log2 bytecode.length)) + 8) + 6 * Nat.log2 bytecode.length + 1)) / 4

open LeanVM.Rpm OracleComp OracleSpec in
/-- **The batching in the random-permutation model.** For a bytecode of power-of-two length and
a bound `M ≤ 2^64 - 1` on the children's count: an adversary of `QA` queries to `π` and `π⁻¹`
outputs a proof; the probability that the batching's verifier, Keccak-256 the sponge over `π` and
Keccak-f[1600] `π`, accepts it while its stream begins with fewer than `M` children of the
bytecode's shapes one of whose claims is false is at most
`(QA + QV + 1) · 2^-191 + 5 (QA + QV)² · 2^-256`, for `QA ≤ 2^128` and the program's query bound
`QV = batchQueryBound bytecode M ≤ 2^96`; the adversary's private coins are free.

This is the batching run outside the circuit, with Keccak-f[1600] = `π`; it does not compose with
the guest program's in-circuit statements, whose `KECCAK` instruction computes the deployed
Keccak-f[1600], so soundness across recursion levels does not follow from it. -/
def BatchSound : Prop :=
  ∀ (M : ℕ) (bytecode : List K), bytecode.length = 2 ^ Nat.log2 bytecode.length →
    M ≤ 2 ^ 64 - 1 → ∀ (A : OracleComp (unifSpec + Common.permSpec KState) (Unit × Proof)) (QA : ℕ),
    Common.IsWeightBound A permQueries QA → QA ≤ 2 ^ 128 → batchQueryBound bytecode M ≤ 2 ^ 96 →
    Pr{let z ← rpmRun A fun z ↦ batchRun queryH queryF (batchAny M bytecode) z.2}[
      z.1.2 = true ∧ FalseChildren bytecode M z.1.1.2] ≤
      (((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ 191 +
        5 * ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

end Batch

end LeanVM.Guest

end
