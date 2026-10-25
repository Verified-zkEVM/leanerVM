module

public import Statement.LeanVm
public import Statement.LeanXmss
public import Statement.LeanSphincs
public import Statement.LeanDa
public import Statement.Data.Bytecode
public import Statement.Fast.Schemes

/-!
# The aggregation guest

The specification of a node of the aggregation (its statement, witness and relation `NodeRel`:
leanXMSS and leanSPHINCS claims, DA claims, children verified by the leanVM verifier with deferred
claims), what a proof of the guest establishes with its witness named (`GuestKnowledge`,
`AggregateSound`), the deployed guest (`LeanVM.Guest.guest`, assembled from the generated
`Statement/Data/`), its completeness on the covered nodes (`GuestCompleteRecursion`,
`GuestCompleteLeaf`, `GuestCompleteCovered`, with the deployed limits they assume) and on its own
honest proofs as children (`GuestChildComplete`), and the recursion step, the batching of
the children's deferred claims sound in the random-permutation model (`BatchSound`, last section:
the batching run outside the circuit with Keccak-f[1600] = `π`, which does not compose with the
guest's in-circuit statements, so soundness across recursion levels does not follow from it).

The soundness statements take the decoder as a parameter: the end theorems name
`LeanVM.Guest.End.decode` (`lean_vm`), which reads the witness off the execution's memory; they
hold of any decoder that outputs valid witnesses, and their content is in the decoder they name.
-/

section

/-!
## The DA claim

LeanDA, the commitment to a blob matrix and the Reed-Solomon membership vector its root
determines, is `LeanDa.lean`'s (the security of the scheme is proved in `lean_da`): its deployed
algorithms (`LeanDa.commitCodewords`, `LeanDa.membershipVector`, `LeanDa.vectorDigest`) are
transcribed there, generic in the hash `H` and in the permutation `P`
of the challenges' duplex sponge. Here the hash is this project's Keccak-256 (`keccak`, from
`keccak256`), its digest read as LeanDA's 32 bytes (`toBytes`), and the permutation is this
project's Keccak-f[1600] on LeanDA's lanes (`keccakLanes`, from `keccakF`): the crate's, at leanVM
`94ee12ff6b2a3d42ba8328e22d09443692e4800b` (`crates/lean_da`, `crates/verifier/src/da.rs`).
`Fast/` (proved `@[csimp]` lemmas, speed only) compiles the field arithmetic on machine words,
Keccak-f[1600] and Keccak-256 with their lanes written out, and the schemes' verifiers with a
constant-depth lookup (`Fast.Schemes`, imported here).

An aggregate's DA claim (`DaClaim`) is a blob's Merkle root (`daRoot`) and the digest of the
root's membership vector (`membershipVectorDigest`); it is held by a matrix committed to the root
whose rows are orthogonal to a vector of that digest (`Witness.Opens`: the guest's
`da_verify`, `crates/rec_aggregation/guests/lean_ethereum.py:3920-4060`). The guest takes the
vector digest from the statement; the outer verifier derives it from the root (`vectorDigestOf`;
`verifier::da::list_digest`, `crates/verifier/src/da.rs:99-104`, called by
`EthereumProof::verify`, `crates/rec_aggregation/src/aggregation.rs:697-719`). The vector digest
is two-level at this pin: the hash of the `128` column digests of `256` entries each
(`LeanDa.vectorDigest`; the guest's `da_vector_cell`, `lean_ethereum.py:4048-4060`).
Orthogonality to the one vector the root determines makes the rows codewords except with the
membership test's soundness error (`lean_da`'s `checker_sound`); that vector is the code's dual
codeword (`lean_da`'s `membershipVector_eq_dual`). The link from this check to `lean_da`'s code
binding is not proved. The prover's copy of the membership vector
(`crates/lean_da/src/membership.rs`) is not transcribed; that it agrees with
`crates/verifier/src/da.rs` is an implementation fact, which honest aggregates rely on.
-/

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- A digest as LeanDA's 32 bytes: its words, little-endian (`Digest.value`). -/
def toBytes (d : Digest) : LeanDa.Digest :=
  ⟨(digestBytes d).toArray, by
    obtain ⟨⟨l⟩, hl⟩ := d
    match l, hl with
    | [_, _, _, _], _ => rfl⟩

/-- Keccak-256 as LeanDA's hash. -/
def keccak (input : List UInt8) : LeanDa.Digest := toBytes (keccak256 input)

/-- LeanDA's sponge lanes as a Keccak state: each `K` word as its 64-bit lane. -/
def lanesState (l : LeanDa.Lanes) : KState := l.map K.lane

/-- A Keccak state as LeanDA's sponge lanes: each 64-bit lane as its `K` word. -/
def stateLanes (s : KState) : LeanDa.Lanes := s.map K.ofLane

/-- Keccak-f[1600] as LeanDA's sponge permutation. -/
def keccakLanes (l : LeanDa.Lanes) : LeanDa.Lanes := stateLanes (keccakF (lanesState l))

/-- **The vector digest of a root**, as the outer verifier derives it
(`vector_digest(membership_vector(root))`, `crates/verifier/src/da.rs:83-104`). -/
def vectorDigestOf (root : Digest) : LeanDa.Digest :=
  LeanDa.vectorDigest keccak (LeanDa.membershipVector keccak keccakLanes (toBytes root))

/-- What holds a DA claim: a matrix of codewords and the vector its rows are orthogonal to. -/
structure Witness where
  /-- The codewords. -/
  rows : List (List K)
  /-- The vector. -/
  vector : List E

/-- **The witness holds the DA claim `⟨root, vd⟩`** (`da_verify`): `1` to `1024` codewords of
`2^15` symbols commit to `root`, and every one is orthogonal to the vector, whose digest is
`vd`. -/
def Witness.Opens (root vd : Digest) (w : Witness) : Prop :=
  1 ≤ w.rows.length ∧ w.rows.length ≤ LeanDa.maxRows ∧
    (∀ row ∈ w.rows, row.length = 2 ^ LeanDa.logM) ∧
    LeanDa.commitCodewords keccak w.rows = toBytes root ∧ w.vector.length = 2 ^ LeanDa.logM ∧
    LeanDa.vectorDigest keccak w.vector = toBytes vd ∧
    ∀ row ∈ w.rows, LeanDa.dot (fun b ↦ w.vector.getD b 0) (fun b ↦ row.getD b 0) = 0

end
end LeanVM.Da

end

section

/-!
## The DA claim, for any hash and permutation

LeanDA (`lean_da`, `LeanDa.Scheme`) defines its algorithms with a pure hash
`H : List UInt8 → Digest` and a pure sponge permutation `P : Lanes → Lanes`. The guest's proofs
also need them answered by a log: every hash and permutation made, then the value. So the
algorithms the DA claim uses are transcribed here in any monad (`…With`): the commitment, the
challenges' duplex sponge (`spongeNewWith`, `spongeDuplexWith`, `spongeAbsorbWith`,
`spongeSampleWith`, `spongeSamplesWith`, LeanDA's `Sponge` operations), the membership vector and
the two-level vector digest; and the deployed padding digests are parameters (`pc`, `pr`;
deployed: the hashes of the zero cell and the zero row, which the guest bakes as constants,
`DA_PAD_CELL_*`, `DA_PAD_ROW_*`, `crates/rec_aggregation/src/aggregation.rs:2575-2578` at leanVM
`94ee12ff6b2a3d42ba8328e22d09443692e4800b`). At `m = Id` they are LeanDA's own
(`commitCodewordsWith_id`, `membershipVectorWith_id`, `vectorDigestWith_id`), and at Keccak-256
and Keccak-f[1600] the deployed DA claim (`vectorDigestOfWith_id`). `Witness.OpensWith` is
`Witness.Opens` over an `Option`-valued hash: it hashes, but runs no sponge. The tree is built
with `nodes.length` as fuel, which is enough (`treeRootFuel_id`).

This project's hash `H : Bytes → m Digest` and permutation `F : KState → m KState` are LeanDA's
through `daHash` (the digest as bytes) and `daPerm` (lanes as `K` words), as `keccak` and
`keccakLanes` are in the DA claim's section above.
-/

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

section With

variable {m : Type → Type} [Monad m] (HD : List UInt8 → m LeanDa.Digest)
  (PD : LeanDa.Lanes → m LeanDa.Lanes)

/-! ### The commitment -/

/-- `LeanDa.listCellDigest` with the hash `HD`. -/
def listCellDigestWith (row : List K) (j : ℕ) : m LeanDa.Digest :=
  HD ((LeanDa.listCell row j).flatMap LeanDa.kBytes)

/-- `LeanDa.rowDigest` with the hash `HD`. -/
def rowDigestWith (row : List K) : m LeanDa.Digest := do
  let ds ← (List.range LeanDa.payloadCells).mapM fun j ↦ listCellDigestWith HD row j
  HD (ds.flatMap fun d ↦ d.toList)

/-- `LeanDa.treeLevel` with the hash `HD`. -/
def treeLevelWith (nodes : List LeanDa.Digest) : m (List LeanDa.Digest) :=
  (List.range (nodes.length / 2)).mapM fun i ↦
    HD (LeanDa.pairBytes (nodes.getD (2 * i) default) (nodes.getD (2 * i + 1) default))

/-- `LeanDa.treeRoot` with the hash `HD`, at most `fuel` levels. -/
def treeRootFuel : ℕ → List LeanDa.Digest → m LeanDa.Digest
  | 0, nodes => pure (nodes.headD default)
  | fuel + 1, nodes =>
    if nodes.length ≤ 1 then pure (nodes.headD default) else do
      let next ← treeLevelWith HD nodes
      treeRootFuel fuel next

/-- `LeanDa.treeRoot` with the hash `HD`. -/
def treeRootWith (nodes : List LeanDa.Digest) : m LeanDa.Digest :=
  treeRootFuel HD nodes.length nodes

/-- **`LeanDa.commitCodewords` with the hash `HD`** and the padding digests `pc` (a zero cell) and
`pr` (a zero row). -/
def commitCodewordsWith (pc pr : LeanDa.Digest) (rows : List (List K)) : m LeanDa.Digest := do
  let n := LeanDa.nPad rows.length
  let rds ← rows.mapM (rowDigestWith HD)
  let rowTree ← treeRootWith HD (rds ++ List.replicate (n - rows.length) pr)
  let cols ← ((List.range LeanDa.cellsPerRow).flatMap fun j ↦
      (List.range n).map fun i ↦ (i, j)).mapM fun ij ↦
    if h : ij.1 < rows.length then listCellDigestWith HD rows[ij.1] ij.2 else pure pc
  let columnTree ← treeRootWith HD cols
  HD (LeanDa.pairBytes rowTree columnTree)

/-! ### The challenges' sponge -/

/-- `LeanDa.Sponge.new` with the permutation `PD`. -/
def spongeNewWith (iv publicInput : LeanDa.Digest) : m LeanDa.Sponge := do
  let state ← PD (Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < 4 then LeanDa.word iv i else if (i : ℕ) < 8 then LeanDa.word publicInput (i - 4)
    else 0)
  pure ⟨state, []⟩

/-- `LeanDa.Sponge.fromLabel` with the hash `HD` and the permutation `PD`. -/
def spongeFromLabelWith (label : List UInt8) : m LeanDa.Sponge := do
  spongeNewWith PD (← HD label) (Vector.replicate 32 0)

/-- `LeanDa.Sponge.duplex` with the permutation `PD`. -/
def spongeDuplexWith (s : LeanDa.Sponge) : m LeanDa.Sponge := do
  let state ← PD (Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < LeanDa.rateLanes then (LeanDa.rateWords s.pending).getD i 0 else s.state[i])
  pure ⟨state, []⟩

/-- `LeanDa.Sponge.absorb` with the permutation `PD`. -/
def spongeAbsorbWith (s : LeanDa.Sponge) (x : E) (tag : K) : m LeanDa.Sponge := do
  let s ← if s.pending.length = LeanDa.rateScalars then spongeDuplexWith PD s else pure s
  pure ⟨s.state, s.pending ++ [(x, tag)]⟩

/-- `LeanDa.Sponge.observe` with the permutation `PD`. -/
def spongeObserveWith (s : LeanDa.Sponge) (x : E) : m LeanDa.Sponge :=
  spongeAbsorbWith PD s x LeanDa.dsObserve

/-- `LeanDa.Sponge.sample` with the permutation `PD`. -/
def spongeSampleWith (s : LeanDa.Sponge) : m (E × LeanDa.Sponge) := do
  let s ← spongeDuplexWith PD s
  pure (LeanDa.ofLimbs s.state[0] s.state[1] s.state[2], s)

/-- `LeanDa.Sponge.samples` with the permutation `PD`. -/
def spongeSamplesWith : ℕ → LeanDa.Sponge → m (List E)
  | 0, _ => pure []
  | n + 1, s => do
    let (c, s) ← spongeSampleWith PD s
    let rest ← spongeSamplesWith n s
    pure (c :: rest)

/-- `LeanDa.membershipChallenges` with the hash `HD` and the permutation `PD`. -/
def membershipChallengesWith (root : LeanDa.Digest) : m (List E) := do
  let s ← spongeFromLabelWith HD PD LeanDa.label
  let s ← spongeObserveWith PD s (LeanDa.ofLimbs (LeanDa.word root 0) (LeanDa.word root 1) 0)
  let s ← spongeObserveWith PD s (LeanDa.ofLimbs (LeanDa.word root 2) (LeanDa.word root 3) 0)
  spongeSamplesWith PD LeanDa.logK s

/-- `LeanDa.membershipVector` with the hash `HD` and the permutation `PD`. -/
def membershipVectorWith (root : LeanDa.Digest) : m (List E) :=
  LeanDa.dualCodeword <$> membershipChallengesWith HD PD root

/-! ### The vector digest -/

/-- `LeanDa.columnDigest` with the hash `HD`. -/
def columnDigestWith (vector : List E) (j : ℕ) : m LeanDa.Digest :=
  HD (LeanDa.limbBytes ((vector.drop (j * LeanDa.cellSymbols)).take LeanDa.cellSymbols))

/-- `LeanDa.vectorDigest` with the hash `HD`: the hash of the column digests. -/
def vectorDigestWith (vector : List E) : m LeanDa.Digest := do
  let ds ← (List.range LeanDa.cellsPerRow).mapM (columnDigestWith HD vector)
  HD (ds.flatMap fun d ↦ d.toList)

end With

/-- This project's hash as LeanDA's: `toBytes` of the answer. -/
def daHash {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (x : List UInt8) :
    m LeanDa.Digest :=
  toBytes <$> H x

/-- This project's permutation as LeanDA's: on the lanes as 64-bit words. -/
def daPerm {m : Type → Type} [Monad m] (F : KState → m KState) (l : LeanDa.Lanes) :
    m LeanDa.Lanes :=
  stateLanes <$> F (lanesState l)

/-- **The vector digest of a root, with the hash `H` and the permutation `F`**
(`vectorDigestOf`). -/
def vectorDigestOfWith {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)
    (F : KState → m KState) (root : Digest) : m LeanDa.Digest := do
  vectorDigestWith (daHash H) (← membershipVectorWith (daHash H) (daPerm F) (toBytes root))

/-- **`Witness.Opens` over an `Option`-valued hash**, the padding digests `pc`, `pr` parameters:
every hash answered, and the claim true of the answers. -/
def Witness.OpensWith (H : List UInt8 → Option Digest) (pc pr : LeanDa.Digest) (root vd : Digest)
    (w : Witness) : Prop :=
  1 ≤ w.rows.length ∧ w.rows.length ≤ LeanDa.maxRows ∧
    (∀ row ∈ w.rows, row.length = 2 ^ LeanDa.logM) ∧
    commitCodewordsWith (daHash H) pc pr w.rows = some (toBytes root) ∧
    w.vector.length = 2 ^ LeanDa.logM ∧
    vectorDigestWith (daHash H) w.vector = some (toBytes vd) ∧
    ∀ row ∈ w.rows, LeanDa.dot (fun b ↦ w.vector.getD b 0) (fun b ↦ row.getD b 0) = 0

/-! ### The deployed algorithms, recovered -/

end
end LeanVM.Da

end

section

/-!
## The aggregation node

Transcribed from leanVM `94ee12ff6b2a3d42ba8328e22d09443692e4800b` (branch `main`),
`crates/rec_aggregation/src/aggregation.rs` (the statement, its digest, the batching, the outer
verifier) and `crates/rec_aggregation/guests/lean_ethereum.py` (the guest); `aggregation.rs:N`
and `lean_ethereum.py:N` below are lines of those files at that commit. The signature schemes,
leanXMSS and leanSPHINCS, are those whose security `lean_xmss` and `lean_sphincs` prove
(`LeanXmss.lean`, `LeanSphincs.lean`), with Keccak-256 as their hash; LeanDA is `LeanDa.lean`'s,
whose security `lean_da` proves (the DA claim's section above).

A node's statement is a list of signature claims, a list of DA claims, and a claim on the
polynomial that the protocol fixes, the guest's stacked bytecode, which the node defers rather
than evaluates (`NodeStatement`). Its public input is the statement's digest under a seed, the
guest's Fiat-Shamir IV (`statementDigest`, `statement_digest`, `aggregation.rs:347-368`,
`lean_ethereum.py:3766-3797`): the Keccak-256 hash of the seed, the signer set's digest and the
DA claims' digest, sixteen bytes a cell, then the deferred claim's cells, three limbs each.

A node holds every claim either directly, by a leanXMSS or leanSPHINCS signature or a blob
matrix, or through a child that makes the same claim. A child is a statement under the same seed
and a proof that the deferring verifier accepts for it
(`LeanVM.Protocol.Verifier.verifyDeferred`, the guest's `verify_sub`). The node batches the
claims that its children's proofs make of the bytecode, with those its children's statements
defer, into its own deferred claim (`batch`: `aggregate_claims`, `lean_ethereum.py:4285-4392`;
`aggregate_deferred_claims`, `aggregation.rs:939-1041`). `NodeRel bytecode seed s w` says all
of it of the statement `s`, with the witness `w` holding every claim; `NodeSpec` is its
existential.

The outer verifier (`verifyAggregate`, `EthereumProof::verify`, `aggregation.rs:697-719`) checks
a proof of the guest on the statement's digest and evaluates the deferred claim itself.

What a valid execution of the guest establishes is `NodeRel` of the witness its memory holds, on
Keccak, as the guest computes it (`GuestKnowledge`, below, with a decoder). The witness is
the knowledge content: `NodeSpec` alone, "some signature verifies", says little, since some
signature verifies for almost every key and message. That the root's `NodeSpec` makes every
claim held at the leaves is a separate argument, conditional on a heuristic: a child's proof is
sound only if Keccak, computed inside the guest, behaves as Keccak-256 and Keccak-f[1600] built
from the random permutation of `LeanVM.KnowledgeSoundness` (`LeanVm.lean`).

**Changes from the leanVM `3f7dc219` transcription.** BLAKE2s is replaced by Keccak-256 (the
hashes) and Keccak-f[1600] (the batching's transcript, a duplex sponge). Flock is gone, so the
deferred claim is the bytecode's alone: a point and a value (`DeferredClaim`,
`aggregation.rs:261-321`), and a proof's claims on the fixed polynomials are its bytecode claim
(`FixedClaims`). The statement's preimage is no longer zero-filled to whole blocks. The batching
runs on the verifier's duplex sponge from the label's hash (`FiatShamirState::from_label`), each
group of absorbed words padded with zeros to a whole rate, and reduces both claims of every child
by one sumcheck.
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ### The signature schemes on Keccak-256 -/

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

/-! ### The statement -/

/-- A leanXMSS key and a message it signed, at a leaf index the claim does not record
(`LeanXmssClaim`, `aggregation.rs:63`). -/
abbrev XmssClaim : Type := LeanXmss.PublicKey × LeanXmss.Message

/-- A leanSPHINCS key and a message it signed (`LeanSphincsClaim`, `aggregation.rs:66`). -/
abbrev SphincsClaim : Type := Sphincs.PublicKey × Sphincs.Message

/-- **A DA claim**: a blob's Merkle root, an entry of an aggregate's `da_roots`
(`aggregation.rs:400-401`; the guest's `da_roots`, `lean_ethereum.py:4151-4154`), with the digest
of the root's membership vector, the vector the blob's rows are orthogonal to. The two are
hashed as `da_claim_cells` and `verifier::da::list_digest` hash them, the root then the vector
digest (`aggregation.rs:563-566`, `crates/verifier/src/da.rs:98-104`): `daListDigest`. -/
structure DaClaim where
  /-- The blob's Merkle root (`da_roots`, `aggregation.rs:401`): the commitment to its matrix of
  codewords (`Da.Witness.Opens`). -/
  daRoot : Digest
  /-- The digest of the root's membership vector (`vector_hash`, `aggregation.rs:564`:
  `vector_digest(membership_vector(root))`, `crates/verifier/src/da.rs:83-96`). The guest takes
  it from the statement; the outer verifier derives it from the root (`Da.vectorDigestOf`,
  `OuterChecks`). -/
  membershipVectorDigest : Digest
  deriving DecidableEq, Inhabited, Repr

/-- A node's claims: leanXMSS claims, leanSPHINCS claims, and DA claims. -/
structure Claims where
  /-- The leanXMSS claims. -/
  xmss : List XmssClaim
  /-- The leanSPHINCS claims. -/
  sphincs : List SphincsClaim
  /-- The DA claims. -/
  da : List DaClaim

/-- The claim the statement defers on the stacked bytecode: its value at a point
(`DeferredClaim`, `aggregation.rs:261-264`). -/
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

/-! ### The deferred claim -/

/-- The deferred claim has the shape of the bytecode `bytecode`: a point of `log₂` of its length
(`bytecode_vars`, `aggregation.rs:824-826`; `BYTECODE_VARS`, `lean_ethereum.py:330`). -/
def DeferredClaim.Shaped (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.bytecodePoint.length = Nat.log2 bytecode.length

/-- **The deferred claim is true** of the bytecode `bytecode`: it has the shape, and the value is
the bytecode's multilinear extension at the point (`DeferredClaim::recompute_scalar`,
`aggregation.rs:282-314`). -/
def DeferredClaim.Holds (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.Shaped bytecode ∧ 2 ^ c.bytecodePoint.length = bytecode.length ∧
    multilinearEval (bytecode.map ofK) c.bytecodePoint = c.bytecodeValue

/-- What a leaf defers: the bytecode at the all-zero point (`DeferredClaim::leaf`,
`aggregation.rs:269-271`; `main`'s leaf branch, `lean_ethereum.py:4266-4274`). The value is
the outer verifier's to check. -/
def DeferredClaim.AtZero (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.bytecodePoint = List.replicate (Nat.log2 bytecode.length) 0

/-- The cells a deferred claim is hashed and absorbed as: the point, then the value
(`DeferredClaim::cells`, `aggregation.rs:316-320`; the guest's `defer_stmt`). -/
def DeferredClaim.cells (c : DeferredClaim) : List E :=
  c.bytecodePoint ++ [c.bytecodeValue]

/-- The cells of a proof's claim on the bytecode, in the order the guest exports them
(`verify_sub`'s `defer_out`, `lean_ethereum.py:3331-3335`): the point (the bus point's row
coordinates, then the selector challenges), then the value. -/
def fixedCells (c : FixedClaims) : List E :=
  c.bytecodePoint ++ [c.bytecodeValue]

/-! ### The statement's digest -/

/-- The 16 bytes of a 128-bit value, least significant byte first: a cell's two limbs. -/
def bytes16 (value : BitVec 128) : List UInt8 := LeanXmss.bytesLE 16 value

/-- A claim as the `64` bytes its list hashes: the key's root and parameter, then the message
(`claim_cells`, `aggregation.rs:221-228`). -/
def claimBytes (root parameter : BitVec 128) (message : BitVec 256) : List UInt8 :=
  bytes16 root ++ bytes16 parameter ++ LeanXmss.bytesLE 32 message

/-- The digest of the leanXMSS claims (`claim_list_digest`, `aggregation.rs:215-217`,
`lean_ethereum.py:3827-3849`). -/
def xmssListDigest (claims : List XmssClaim) : Digest :=
  keccak256 (claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2)

/-- The digest of the leanSPHINCS claims (`claim_list_digest`). -/
def sphincsListDigest (claims : List SphincsClaim) : Digest :=
  keccak256 (claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2)

/-- **The signer set's digest** (`signers_hash`, `aggregation.rs:242-251`): the hash of the two
lists' digests. Each binds its list's length through Keccak's padding. -/
def signersDigest (xmss : List XmssClaim) (sphincs : List SphincsClaim) : Digest :=
  keccak256 (digestBytes (xmssListDigest xmss) ++ digestBytes (sphincsListDigest sphincs))

/-- The DA claims' digest: each root, then its vector digest (`da_list_digest` in the guest,
`lean_ethereum.py:4063-4075`; the outer verifier's `verifier::da::list_digest` derives the vector
digests from the roots). -/
def daListDigest (claims : List DaClaim) : Digest :=
  keccak256 (claims.flatMap fun c ↦ digestBytes c.daRoot ++ digestBytes c.membershipVectorDigest)

/-- The 24 bytes of a field element, its three limbs. -/
def eBytes (x : E) : List UInt8 := kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2)

/-- **The statement's digest under `seed`** (`statement_digest`, `aggregation.rs:347-368`,
`lean_ethereum.py:3766-3797`): the Keccak-256 hash of the seed, the signer set's digest and the
DA claims' digest, then the deferred claim's cells, an odd count paired with a zero cell. The
cells carry no lengths: the digest tells two deferred claims apart only at one shape. -/
def statementDigest (seed : Digest) (s : NodeStatement) : Digest :=
  let cells := s.defer.cells ++ if s.defer.cells.length % 2 = 1 then [0] else []
  keccak256 (digestBytes seed ++ digestBytes (signersDigest s.claims.xmss s.claims.sphincs) ++
    digestBytes (daListDigest s.claims.da) ++ cells.flatMap eBytes)

/-! ### Batching the deferred claims (`aggregate_claims`, `aggregate_deferred_claims`) -/

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
`aggregation.rs:949-953`; `AGG_CHILD_PAD`). -/
def padRate (words : List E) : List E :=
  words ++ List.replicate ((rateScalars - words.length % rateScalars) % rateScalars) 0

/-- The rounds of a batching sumcheck from the running claim: each round absorbs `g(1)` and
`g(∞)`, squeezes the challenge, and folds the degree-2 round polynomial whose `g(0)` the claim
fixes (`batch_sumcheck`, `lean_ethereum.py:1007-1024`; `absorb_round`,
`aggregation.rs:880-896`). The challenges and the final claim. -/
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

/-- The batching transcript's label (`RECURSION_AGG_LABEL`, `aggregation.rs:72`). -/
def batchLabel : List UInt8 := "leanvm/recursion-aggregation/v1".toUTF8.toList

/-- The batching transcript's initial state (`FiatShamirState::from_label`): Keccak-f of the
label's hash in lanes `0..4`, the other lanes zero. The guest bakes its capacity (`AGG_SEED_*`,
`aggregation.rs:2557-2560`). -/
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

/-! ### The node -/

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
  | .direct w => w.Opens claim.daRoot claim.membershipVectorDigest
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

/-! ### The outer verifier -/

/-- The guest's deployed seed: its Fiat-Shamir IV (`fs_seed`,
`crates/leanvm_core/src/cpu/mod.rs:68-80`). -/
abbrev deployedSeed (guest : Program) : Digest := fiatShamirIv (bytecodeWords guest)

/-- **What the outer verifier checks of a statement besides its proof**: every DA claim's vector
digest is its root's, and the deferred claim holds of the guest's bytecode. -/
def OuterChecks (guest : Program) (s : NodeStatement) : Prop :=
  (∀ c ∈ s.claims.da, Da.toBytes c.membershipVectorDigest = Da.vectorDigestOf c.daRoot) ∧
    s.defer.Holds (bytecodeWords guest)

/-- **The outer verifier** of an aggregate of the guest `guest` (`EthereumProof::verify`,
`aggregation.rs:697-719`): every DA claim's vector digest is its root's, the deferred claim holds,
and the proof verifies on the statement's digest under the guest's IV. It omits the deployed
verifier's checks on the lists' form (`check_signer_set`, `check_da_roots`,
`aggregation.rs:543-561`: each list sorted without repeats, fewer than `2^16` signature claims
and at most `16` DA roots), so it accepts more. -/
def verifyAggregate (guest : Program) (s : NodeStatement) (π : Proof) : Prop :=
  OuterChecks guest s ∧
    Verifier.verify (bytecodeWords guest) (statementDigest (deployedSeed guest) s) π = true

end
end LeanVM.Node

end

section

/-!
## The node, for any hash and permutation

The section above states what a node establishes with Keccak-256 and Keccak-f[1600]. The guest's
proofs also need it relative to a hash and a permutation answered by a log: every hash and
permutation a check makes must be answered, and the check must hold for the answers. So every
hashing function of that section is given here with the hash `H : Bytes → m Digest` and the
permutation `F : KState → m KState` in any monad (`…With`), as the verifier is (`verifier H F`,
`LeanVm.lean`): at `m = Id`, `H = keccak256` and `F = keccakF` it is the deployed one
(`statementDigestWith_id`, `batchWith_id`, `xmssVerifyWith_id`, …), and at `m = Option` with `H` and
`F` a log's lookups it is the computation answered by the log. The digests and the signature schemes
use only `H`; the batching's transcript, a duplex sponge, only `F`, from a parameter state `s0`
(deployed: `batchSeed`, Keccak-f of the label's hash, whose capacity the guest bakes as
`AGG_SEED_*`). `NodeRelWith H F` is `NodeRel` over an `Option`-valued hash and permutation, each
check "answered and true".

The deployed definitions are not changed: this section only adds to them.
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section With

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KState → m KState)

/-! ### The signature schemes -/

/-- leanXMSS verification with the hash `H`. -/
def xmssVerifyWith (pk : LeanXmss.PublicKey) (message : LeanXmss.Message)
    (σ : LeanXmss.Signature) : m Bool :=
  letI : HasQuery LeanXmss.HashSpec m := ⟨fun x ↦ digestBits <$> H x⟩
  LeanXmss.Concrete.verify pk message σ

/-- leanSPHINCS verification with the hash `H`. -/
def sphincsVerifyWith (pk : Sphincs.PublicKey) (message : Sphincs.Message)
    (σ : Sphincs.Signature) : m Bool :=
  letI : HasQuery Sphincs.HashSpec m := ⟨fun x ↦ digestBits <$> H x⟩
  Sphincs.Concrete.verify pk message σ

/-! ### The statement's digest -/

/-- `xmssListDigest` with the hash `H`. -/
def xmssListDigestWith (claims : List XmssClaim) : m Digest :=
  H (claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2)

/-- `sphincsListDigest` with the hash `H`. -/
def sphincsListDigestWith (claims : List SphincsClaim) : m Digest :=
  H (claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2)

/-- `signersDigest` with the hash `H`. -/
def signersDigestWith (xmss : List XmssClaim) (sphincs : List SphincsClaim) : m Digest := do
  let x ← xmssListDigestWith H xmss
  let s ← sphincsListDigestWith H sphincs
  H (digestBytes x ++ digestBytes s)

/-- `daListDigest` with the hash `H`. -/
def daListDigestWith (claims : List DaClaim) : m Digest :=
  H (claims.flatMap fun c ↦ digestBytes c.daRoot ++ digestBytes c.membershipVectorDigest)

/-- **`statementDigest` with the hash `H`.** -/
def statementDigestWith (seed : Digest) (s : NodeStatement) : m Digest := do
  let sd ← signersDigestWith H s.claims.xmss s.claims.sphincs
  let dd ← daListDigestWith H s.claims.da
  let cells := s.defer.cells ++ if s.defer.cells.length % 2 = 1 then [0] else []
  H (digestBytes seed ++ digestBytes sd ++ digestBytes dd ++ cells.flatMap eBytes)

/-! ### The batching -/

/-- A Fiat-Shamir chain with the permutation `F`. -/
abbrev ChainWith : Type → Type := StateT Sponge m

/-- `observe` with the permutation `F`. -/
def observeWith (x : E) : ChainWith (m := m) Unit := do
  set (← (Compile.absorb F (← get) x dsObserve : m Sponge))

/-- `sample` with the permutation `F`. -/
def sampleWith : ChainWith (m := m) E := do
  let (c, sp) ← (Compile.squeeze F (← get) : m (E × Sponge))
  set sp
  return c

/-- `batchRounds` with the permutation `F`. -/
def batchRoundsWith : E → List (E × E) → ChainWith (m := m) (List E × E)
  | claim, [] => return ([], claim)
  | claim, (g1, gInf) :: rest => do
    observeWith F g1
    observeWith F gInf
    let r ← sampleWith F
    let g0 := claim + g1
    let (rs, final) ← batchRoundsWith ((gInf * r + (g0 + g1 + gInf)) * r + g0) rest
    return (r :: rs, final)

/-- `batchSeed` with the hash `H` and the permutation `F`. -/
def batchSeedWith : m KState := do
  F (seedInput (← H batchLabel) (Vector.replicate 4 0))

/-- **`batch` with the permutation `F`, from the sponge state `s0`** (deployed: `batchSeed`). -/
def batchWith (s0 : KState) (children : List ChildClaims) (h : BatchHints) :
    m (Option DeferredClaim) :=
  go.run' ⟨s0, []⟩
where
  /-- The transcript. -/
  go : ChainWith (m := m) (Option DeferredClaim) := do
    for x in padRate [gpow children.length] do observeWith F x
    for c in children do
      for x in padRate c.words do observeWith F x
    let mut lambdas : List (E × E) := []
    for _ in children do
      let lf ← sampleWith F
      let lc ← sampleWith F
      lambdas := lambdas ++ [(lf, lc)]
    let claim := sumE (List.zipWith (fun c l ↦
      l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) children lambdas)
    let (r, final) ← batchRoundsWith F claim h.bytecodeRounds
    let weight := sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.fresh.bytecodePoint r + l.2 * eqEval c.carried.bytecodePoint r)
      children lambdas)
    if final = h.bytecodeValue * weight then return some ⟨r, h.bytecodeValue⟩
    else return none

end With

/-! ### The node relation over an answered hash and permutation -/

section Answered

variable (H : Bytes → Option Digest) (F : KState → Option KState)

/-- The leanXMSS claim is held: by a signature verified with every hash answered, or by a child
making it. -/
def XmssHeldWith (children : List Child) (claim : XmssClaim) : Holder LeanXmss.Signature → Prop
  | .direct σ => xmssVerifyWith H claim.1 claim.2 σ = some true
  | .child i => ∃ c, children[i]? = some c ∧ claim ∈ c.statement.claims.xmss

/-- The leanSPHINCS claim is held: by a signature verified with every hash answered, or by a child
making it. -/
def SphincsHeldWith (children : List Child) (claim : SphincsClaim) :
    Holder Sphincs.Signature → Prop
  | .direct σ => sphincsVerifyWith H claim.1 claim.2 σ = some true
  | .child i => ∃ c, children[i]? = some c ∧ claim ∈ c.statement.claims.sphincs

/-- The DA claim is held: by a matrix opening with every hash answered (the padding digests
`pc`, `pr`), or by a child making it. -/
def DaHeldWith (pc pr : LeanDa.Digest) (children : List Child) (claim : DaClaim) :
    Holder Da.Witness → Prop
  | .direct w => w.OpensWith H pc pr claim.daRoot claim.membershipVectorDigest
  | .child i => ∃ c, children[i]? = some c ∧ claim ∈ c.statement.claims.da

/-- The children's claims the batching absorbs, their public inputs the answered digests of their
statements. -/
def childClaimsWith (seed : Digest) (children : List Child) : Option (List ChildClaims) :=
  children.mapM fun c ↦ (fun pi ↦ ⟨pi, c.fresh, c.statement.defer⟩) <$>
    statementDigestWith H seed c.statement

/-- **`NodeRel` over an answered hash and permutation**: what the witness `w` establishes of `s`
when every hash and permutation the guest computes is answered by `H` and `F` (a log's lookups) —
every check of `NodeRel` with its hashes and permutations answered and true; the batching from
the sponge state `s0`; the DA padding digests `pc`, `pr`. -/
def NodeRelWith (s0 : KState) (pc pr : LeanDa.Digest) (bytecode : List K) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) : Prop :=
  s.defer.Shaped bytecode ∧
  (∀ c ∈ w.children, c.statement.defer.Shaped bytecode ∧ ∃ pi,
    statementDigestWith H seed c.statement = some pi ∧
    verifyDeferredWith H F bytecode seed pi c.fresh c.proof = some true) ∧
  List.Forall₂ (XmssHeldWith H w.children) s.claims.xmss w.xmss ∧
  List.Forall₂ (SphincsHeldWith H w.children) s.claims.sphincs w.sphincs ∧
  List.Forall₂ (DaHeldWith H pc pr w.children) s.claims.da w.da ∧
  if w.children = [] then s.defer.AtZero bytecode
  else ∃ cs, childClaimsWith H seed w.children = some cs ∧
    batchWith F s0 cs w.hints = some (some s.defer)

end Answered

/-! ### The deployed functions, recovered -/

end
end LeanVM.Node

end

section

/-!
## The aggregation guest, its witness named

`NodeSpec` (above) is the existential `∃ w, NodeRel …`. A hash-based witness (a signature, a
child's proof, a blob matrix) exists for nearly every claim, so "some witness holds the statement"
says little. What a valid execution of the guest establishes is more: its memory holds the
witness. A **decoder** reads a seed, a statement and a witness off a memory (`Decoder`,
`Decoded`), and the guest's soundness is stated for it:

* `GuestKnowledge guest decode`: every valid execution of `guest` on a public input decodes to a
  statement of that input's digest under the decoded seed, and a witness holding it;
* `AggregateSound guest decode` (below), what a consumer learns, in the random-permutation
  model of `LeanVm.lean`: the verifier accepts a proof of `guest` on the digest of
  a statement `s` under the deployed seed, `s` passing the outer verifier's other checks
  (`OuterChecks`), while the execution the knowledge extractor `extractorRpm` reads off the proof
  and the adversary's transcript is none, or does not explain `s` (`Explains`: decode to the
  deployed seed, `s` and a witness holding it, or give a Keccak-256 collision among
  `collisionCandidates`), with probability at most the bound of `KnowledgeSoundness`.

Both hold of any decoder that happens to output valid witnesses; their content is in the decoder
the theorems name (`LeanVM.Guest.End.decode`), which reads every component off the memory: the
statement from `main`'s frame, each signature, matrix and child proof from the frame of the
function that checked it, the first frame of the memory at which that function's code holds on
the call's words. The decoder chooses nothing. It computes no hash and runs no verifier of its own;
it finds each call's frame as the first of the memory's `2^κ` frames at which the guest's own code
for the callee holds on the call's words (a classical test of the guest's semantics, which
includes its in-circuit checks), and reads the witness there. The seed is the guest's hint:
the statement's digest binds it, so a consumer comparing the digest with its own statement's under
the deployed seed learns both, unless it holds a Keccak-256 collision.

At leanVM `94ee12ff6b2a3d42ba8328e22d09443692e4800b` the statement's preimage is hashed as it is,
without the zero fill to whole blocks that BLAKE2s had (`statement_digest`,
`crates/rec_aggregation/src/aggregation.rs:347-368`): `statementPreimage` is those bytes, and the
former `statementBytes` (the bytes before the fill) is gone.
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open scoped ENNReal

@[expose] public section

/-! ### The bytes each digest hashes, and the candidate collisions -/

/-- The deferred claim's cells, an odd count paired with a zero cell. -/
def paddedCells (c : DeferredClaim) : List E :=
  c.cells ++ if c.cells.length % 2 = 1 then [0] else []

/-- The bytes `statementDigest seed s` hashes: the seed, the signer set's and the DA claims'
digests, then the padded deferred cells. -/
def statementPreimage (seed : Digest) (s : NodeStatement) : List UInt8 :=
  digestBytes seed ++ digestBytes (signersDigest s.claims.xmss s.claims.sphincs) ++
    digestBytes (daListDigest s.claims.da) ++ (paddedCells s.defer).flatMap eBytes

/-- The bytes `signersDigest xmss sphincs` hashes. -/
def signersPreimage (xmss : List XmssClaim) (sphincs : List SphincsClaim) : List UInt8 :=
  digestBytes (xmssListDigest xmss) ++ digestBytes (sphincsListDigest sphincs)

/-- The bytes `xmssListDigest claims` hashes. -/
def xmssPreimage (claims : List XmssClaim) : List UInt8 :=
  claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2

/-- The bytes `sphincsListDigest claims` hashes. -/
def sphincsPreimage (claims : List SphincsClaim) : List UInt8 :=
  claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2

/-- The bytes `daListDigest claims` hashes. -/
def daPreimage (claims : List DaClaim) : List UInt8 :=
  claims.flatMap fun c ↦ digestBytes c.daRoot ++ digestBytes c.membershipVectorDigest

/-- **The candidate collisions** of two statements' digests: the pairs of inputs of the five
hashes the digests compute, the outer one, the signer set's, the two claim lists' and the DA
list's. -/
def collisionCandidates (seed : Digest) (s : NodeStatement) (seed' : Digest)
    (s' : NodeStatement) : List (List UInt8 × List UInt8) :=
  [(statementPreimage seed s, statementPreimage seed' s'),
    (signersPreimage s.claims.xmss s.claims.sphincs,
      signersPreimage s'.claims.xmss s'.claims.sphincs),
    (xmssPreimage s.claims.xmss, xmssPreimage s'.claims.xmss),
    (sphincsPreimage s.claims.sphincs, sphincsPreimage s'.claims.sphincs),
    (daPreimage s.claims.da, daPreimage s'.claims.da)]

/-- **A collision**: a pair of different inputs with the same Keccak-256 digest, among
`pairs`. -/
def HasCollision (pairs : List (List UInt8 × List UInt8)) : Prop :=
  ∃ p ∈ pairs, p.1 ≠ p.2 ∧ keccak256 p.1 = keccak256 p.2

/-! ### Decoders -/

/-- What a decoder reads off a memory: a seed, a statement and a witness. -/
structure Decoded where
  /-- The seed. -/
  seed : Digest
  /-- The statement. -/
  statement : NodeStatement
  /-- The witness. -/
  witness : NodeWitness

/-- A decoder: from a memory, a seed, a statement and a witness. -/
abbrev Decoder : Type := ∀ {κ : ℕ}, MemImage κ → Decoded

/-! ### What a proof of the guest establishes -/

/-- **What a valid execution of `guest` on `input` decodes to** (`d`): a statement of the input's
digest under the decoded seed, and a witness holding it for the guest's bytecode. -/
def DecodesOn (guest : Program) (input : PublicInput) (d : Decoded) : Prop :=
  statementDigest d.seed d.statement = publicDigest input ∧
    NodeRel (bytecodeWords guest) d.seed d.statement d.witness

/-- **Knowledge soundness of the guest, its witness named**: every valid execution decodes. -/
def GuestKnowledge (guest : Program) (decode : Decoder) : Prop :=
  ∀ input (t : Trace guest), ValidExecution guest input t → DecodesOn guest input (decode t.image)

/-- **The decoding `d` explains the statement `s`**: it is the deployed seed, `s` and a witness
holding `s`; or the decoded seed and statement, with the deployed seed and `s`, give a Keccak-256
collision among the candidates. -/
def Explains (guest : Program) (s : NodeStatement) (d : Decoded) : Prop :=
  (d.seed = deployedSeed guest ∧ d.statement = s ∧
      NodeRel (bytecodeWords guest) (deployedSeed guest) s d.witness) ∨
    HasCollision (collisionCandidates d.seed d.statement (deployedSeed guest) s)

end
end LeanVM.Node

end

@[expose] public section

/-!
## The outer verifier's acceptance, explained

`AggregateSound guest decode`: in the random-permutation experiment of `LeanVm.lean`
(`rpmExperiment`), the verifier accepts a proof of `guest` on the digest, under the deployed seed,
of a statement `s` that passes the outer verifier's other checks (`OuterChecks`, above),
while the execution the knowledge extractor `extractorRpm` reads off the proof and the adversary's
transcript is none, or does not explain `s` (`Explains`, above: decode to the deployed
seed, `s` and a witness holding it, or give a Keccak-256 collision among `collisionCandidates`),
with probability at most `(Q + 2^14) · 2^-128 + 7 (Q + 2^14)² · 2^-256`, the bound of
`KnowledgeSoundness`, for an adversary of at most `Q ≤ 2^128` queries to `π` and `π⁻¹`.

Keccak-256 and Keccak-f[1600] outside the executed program are built from the random permutation;
the statement's digest and the collisions are of the deployed Keccak-256, which the guest
computes.
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

/-- **The outer verifier's acceptance, explained.** The adversary, querying `π` and `π⁻¹`,
outputs a proof. The event: the verifier accepts it as a proof of `guest` on the digest, under
the deployed seed, of a statement `s` that passes the outer verifier's other checks, and yet the
execution the knowledge extractor `extractorRpm` reads off the adversary's transcript and the
proof does not explain `s`. Its probability is at most the bound of `KnowledgeSoundness`,
`(Q + 2^14) · 2^-128 + 7 (Q + 2^14)² · 2^-256`, for an adversary of at most `Q ≤ 2^128` queries. -/
def AggregateSound (guest : Program) (decode : Decoder) : Prop :=
  ∀ (A : RpmAdversary) (Q : ℕ), A.IsTotalQueryBound Q → Q ≤ 2 ^ 128 →
    Pr{let z ← rpmExperiment A}[∃ s : NodeStatement, z.accepted ∧ z.program = guest ∧
      publicDigest z.input = statementDigest (deployedSeed guest) s ∧ OuterChecks guest s ∧
      ¬ ∃ t, extractorRpm z.program z.input z.transcript z.proof = some t ∧
        Explains guest s (decode t.image)] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        7 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM.Node

end

/-! ## The deployed guest -/

section

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The aggregation guest's bytecode. -/
def guest : Program := assemble Data.functions 19 (by decide)

end
end LeanVM.Guest

end

section

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The guest's bytecode, as the verifier and `NodeSpec` read it. -/
abbrev bytecode : List K := bytecodeWords guest

/-- The public input a digest is: its four words, the digest's halves in memory words `0` and `1`
(`Front.publicInputOfDigest`). -/
abbrev publicInputOf (d : Digest) : PublicInput := EndToEnd.Front.publicInputOfDigest d

end
end LeanVM.Guest.End

end

/-! ## The honest streams' plan, which the limits read -/

section

namespace LeanVM.Guest.Hints

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- `STREAM_CAP` (`aggregation.rs:1392`): a child's proof stream is zero-padded to it. -/
def streamCap : ℕ := 8192

/-- `MU_MIN` (`aggregation.rs:1383`): the least stack log the guest has an opening arm for. -/
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

/-- One region of the coverage table: its duplicate claims, and the slot of every raw claim and
of every child's claims. -/
structure Region (α : Type) where
  /-- The duplicate claims, in slot order. -/
  dups : List α
  /-- The raw claims' slots. -/
  raw : List ℕ
  /-- Per child, its claims' slots. -/
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

/-- DA claims are equal when their roots and their vector digests are. -/
instance : BEq DaClaim := ⟨fun a b ↦ a.daRoot.toList == b.daRoot.toList &&
  a.membershipVectorDigest.toList == b.membershipVectorDigest.toList⟩

/-- The deferring verifier's initial state on a child's proof under the node's seed
(`verifyDeferredWith`). -/
def childStart (seed : Digest) (c : Child) : St :=
  ⟨⟨keccakF (seedInput seed (statementDigest seed c.statement)), []⟩, c.proof.stream,
    c.proof.openings, []⟩

end
end LeanVM.Guest.Hints

end

section

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **A child's announced stack log and rate** (`readSizes`, `Verifier.announced`): the opening
arm its `verify_sub` dispatches to (G:3314-3316); `(0, 0)` if its stream announces none, which no
child of a node within `Limits`, its caps agreeing and no zero challenge, does
(`B1.Main.childShape_bounds`). -/
def childShape (bytecode : List K) (c : Child) : ℕ × ℕ :=
  match announced bytecode c.proof.stream with
  | some (layout, r) => (layout.stackLog, r)
  | none => (0, 0)

end
end LeanVM.Guest

end

/-! ## The deployed limits -/

section

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

namespace Limits

/-- `foldRounds` refusing a zero challenge. -/
def foldRoundsNZ : ℕ → WhirState → List E → Prog (WhirState × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    let challenge ← Prog.sampleE
    Prog.require (challenge ≠ 0)
    let target := polyEval s.quad challenge
    let quad ← sumcheckRoundPoly 3 target none
    foldRoundsNZ n { s with target, quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge])

/-- `tailRounds` refusing a zero challenge. -/
def tailRoundsNZ : ℕ → E → List E → Prog (List E × E)
  | 0, target, _ => return ([], target)
  | n + 1, _, quad => do
    let challenge ← Prog.sampleE
    Prog.require (challenge ≠ 0)
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRoundsNZ n target quad
      return (challenge :: rest, target)

/-- `whirLevels` refusing a zero fold, tail or level batching challenge. -/
def whirLevelsNZ (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirState → Prog Unit
  | _, [], _ => Prog.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRoundsNZ level.fold s []
    let messageLog := logN - s.folds.length
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← Prog.readN (2 ^ messageLog)
        pure (residual, ([] : List (E × List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        Prog.commitP height width
        let oodPoint ← Prog.sampleN messageLog
        let oodValue ← Prog.readE
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(oodValue, intro, fun x ↦ eqEval oodPoint x)])
    Prog.grindP Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← Prog.sampleE
    Prog.require (lam ≠ 0)
    let queryWeights := powers lam queries.length
    let words ← Prog.queryP index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++
      [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glue lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRoundsNZ messageLog s.target s.quad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      Prog.require (terminal = target)
    | _ :: _ => whirLevelsNZ logN laneFolds evaluateBasis (index + 1) rest s

/-- `verifyWhir` refusing a zero fold, tail or level batching challenge. -/
def verifyWhirNZ (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : Prog Unit := do
  let config ← liftOption (deriveConfig logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevelsNZ logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config
    ⟨target, quad, [], []⟩

/-- `verifyStackedOpening` refusing a zero fold, tail or level batching challenge. -/
def verifyStackedOpeningNZ (stackLog logInvRate : ℕ) (claims : List StackClaim) : Prog Unit := do
  let scales := powers (← Prog.sampleE) claims.length
  verifyWhirNZ stackLog logInvRate (dot scales (claims.map (·.2)))
    fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-- `verifyExecution` whose stacked opening refuses a zero fold, tail or level batching
challenge. -/
def verifyExecutionNZ (ev : Evaluations) (bytecode : List K) (publicInput : Digest) :
    Prog Unit := do
  let (layout, logInverseRate) ← readSizes bytecode
  commitStack layout.stackLog logInverseRate
  let bus ← verifyBusBalance ev layout
  let claims ← tablePhase layout bus
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (claims, keccakPoint, keccakSlices) ← keccakPhase layout claims
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpeningNZ layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.onStack layout))

/-- `deferredProgram` whose stacked opening refuses a zero fold, tail or level batching
challenge. -/
def deferredProgramNZ (c : FixedClaims) (bytecode : List K) (publicInput : Digest) :
    Prog Bool := do
  verifyExecutionNZ (.claimed c) bytecode publicInput
  return true

/-- **The deployed deferring verifier refusing a zero challenge where the guest divides**:
`verifyDeferred` with `deferredProgramNZ`. -/
def verifyDeferredNZ (bytecode : List K) (iv publicInput : Digest) (c : FixedClaims)
    (π : Proof) : Bool :=
  Id.run (runProof (m := Id) keccak256 keccakF (deferredProgramNZ c bytecode publicInput)
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

open Limits

/-- **No zero challenge where the guest divides** (`G:1253, 1560, 1565`): every child's proof is
accepted by the deferring verifier whose stacked opening also refuses a zero fold challenge, a
zero tail challenge and a zero level batching challenge `λ`, under the node's seed. -/
def NoZeroChallenge (bytecode : List K) (seed : Digest) (w : NodeWitness) : Prop :=
  ∀ c ∈ w.children,
    verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true

/-- **A child's openings agree in the guest's Merkle caps**: at every query step of each child's
deferring verifier, run under the node's seed, the step's openings agree wherever they meet. One
tree's openings, the honest prover's, agree. -/
def CapsAgree (bytecode : List K) (seed : Digest) (w : NodeWitness) : Prop :=
  ∀ c ∈ w.children, ∀ b ∈ queriesOf
      (deferredProgram c.fresh bytecode (statementDigest seed c.statement)) (Hints.childStart seed c),
    BatchAgrees b.1 b.2

open Hints in
/-- The coverage table's slots (`n_total`, G:4135): each region's declared claims and its
duplicates, as `honestPushes` plans them. -/
def coverage (s : NodeStatement) (w : NodeWitness) : ℕ :=
  let ch := w.children
  s.claims.xmss.length + (plan s.claims.xmss ((direct s.claims.xmss w.xmss).map (·.1))
      (ch.map (·.statement.claims.xmss))).dups.length +
    s.claims.sphincs.length + (plan s.claims.sphincs ((direct s.claims.sphincs w.sphincs).map (·.1))
      (ch.map (·.statement.claims.sphincs))).dups.length +
    s.claims.da.length + (plan s.claims.da ((direct s.claims.da w.da).map (·.1))
      (ch.map (·.statement.claims.da))).dups.length

open Hints in
/-- **The deployed limits** (the triage's findings), where `NodeRel` admits witnesses the guest
cannot run. Implied by these, with `NodeRel`, and so not limits of their own: a child's stack log
at most `28` and rate in `[1, 4]` (`readSizes`), the duplicate DA slots below `258` (G:4127-4129),
every count of `meta` below `2^16` (G:4114-4119), the bus depth at most `32` (G:1630), the tables'
heights at most `28` (G:2010). -/
structure Limits (bytecode : List K) (s : NodeStatement) (w : NodeWitness) : Prop where
  /-- 1. A child's stack log is at least `MU_MIN = 22`: the guest has one opening arm per stack
  log in `[22, 28]` (G:3314-3316); the Spec admits `15`. -/
  stackLog : ∀ c ∈ w.children, ∀ layout r, announced bytecode c.proof.stream = some (layout, r) →
    muMin ≤ layout.stackLog
  /-- 2. A child's proof stream is at most `STREAM_CAP = 8192` scalars (G:3165). -/
  stream : ∀ c ∈ w.children, c.proof.stream.length ≤ streamCap
  /-- 3. At most one DA claim is held directly (G:4121). -/
  directDa : (direct s.claims.da w.da).length ≤ 1
  /-- 4. A claim declared `n` times is held `n` times, by witnesses or by distinct entries of the
  children's lists: each coverage slot is written once (G:3871-3872, 4080-4081, 4262), where
  `NodeRel` lets two equal claims share one holder. -/
  xmssHeld : ∀ x, s.claims.xmss.count x ≤ ((direct s.claims.xmss w.xmss).map (·.1)).count x +
    (w.children.map fun c ↦ c.statement.claims.xmss.count x).sum
  sphincsHeld : ∀ x, s.claims.sphincs.count x ≤ ((direct s.claims.sphincs w.sphincs).map (·.1)).count x +
    (w.children.map fun c ↦ c.statement.claims.sphincs.count x).sum
  daHeld : ∀ x, s.claims.da.count x ≤ ((direct s.claims.da w.da).map (·.1)).count x +
    (w.children.map fun c ↦ c.statement.claims.da.count x).sum
  /-- 5. At most `MAX_RECURSIONS = 16` children (G:4120). -/
  children : w.children.length ≤ 16
  /-- 5. At most `MAX_DA_ROOTS = 16` DA claims in the statement and in each child (G:4126,
  4246). -/
  daRoots : s.claims.da.length ≤ 16 ∧ ∀ c ∈ w.children, c.statement.claims.da.length ≤ 16
  /-- 5. Every child's signature list below `2^16` (G:4233-4234). -/
  lists : ∀ c ∈ w.children, c.statement.claims.xmss.length < 2 ^ 16 ∧
    c.statement.claims.sphincs.length < 2 ^ 16
  /-- 5. The coverage table below `2^16` (G:4135-4136). -/
  coverage : coverage s w < 2 ^ 16
  /-- 6. At least one declared claim (G:4174). -/
  nonempty : 0 < s.claims.xmss.length + s.claims.sphincs.length + s.claims.da.length

end
end LeanVM.Guest

end

/-! ## A node's work -/

section

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open scoped ENNReal

@[expose] public section

/-- **A node's work**: what the size of its run grows with. -/
structure Work where
  /-- The declared claims, of the three lists. -/
  declared : ℕ
  /-- The coverage table's slots. -/
  coverage : ℕ
  /-- The raw leanXMSS signatures. -/
  rawXmss : ℕ
  /-- The raw leanSPHINCS signatures. -/
  rawSphincs : ℕ
  /-- The blob matrices held directly. -/
  rawDa : ℕ
  /-- Their rows: the blobs held directly. -/
  rawDaRows : ℕ
  /-- The children. -/
  children : ℕ
  /-- The children's declared claims, of the three lists. -/
  childClaims : ℕ
  /-- Each child's announced stack log and rate (`childShape`). -/
  childShapes : List (ℕ × ℕ)

/-- The work of the node `s` with the witness `w`. -/
def work (s : NodeStatement) (w : NodeWitness) : Work where
  declared := s.claims.xmss.length + s.claims.sphincs.length + s.claims.da.length
  coverage := coverage s w
  rawXmss := (Hints.direct s.claims.xmss w.xmss).length
  rawSphincs := (Hints.direct s.claims.sphincs w.sphincs).length
  rawDa := (Hints.direct s.claims.da w.da).length
  rawDaRows := ((Hints.direct s.claims.da w.da).map fun p ↦ p.2.rows.length).sum
  children := w.children.length
  childClaims := (w.children.map fun c ↦ c.statement.claims.xmss.length +
    c.statement.claims.sphincs.length + c.statement.claims.da.length).sum
  childShapes := w.children.map (childShape bytecode)

end
end LeanVM.Guest.End

end

@[expose] public section

/-! ### The guest's completeness on the covered nodes -/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (work bytecode publicInputOf)

/-- **Every recursion node of at most `2048` claims has a valid execution of the guest**: for
every seed, statement `s` and witness `w` with `NodeRel`, within the deployed limits (so at most
`16` children, each at one of the guest's opening arms), the caps agreeing and no zero challenge
where the guest divides, holding no raw leanXMSS or leanSPHINCS signature and no blob directly,
with at most `2048` declared claims, coverage slots and children's claims, there is a valid
execution of the guest on the statement's digest of committed size in `[2^22, 2^28]`. Proved by
`LeanVM.Guest.Budget.guest_complete_recursion`. -/
abbrev GuestCompleteRecursion : Prop :=
  ∀ (seed : Digest) (s : NodeStatement) (w : NodeWitness),
    NodeRel bytecode seed s w → Limits bytecode s w →
    CapsAgree bytecode seed w → NoZeroChallenge bytecode seed w →
    (work s w).rawXmss = 0 → (work s w).rawSphincs = 0 → (work s w).rawDa = 0 →
    (work s w).declared ≤ 2048 → (work s w).coverage ≤ 2048 →
    (work s w).childClaims ≤ 2048 →
    ∃ t : Trace guest, ValidExecution guest (publicInputOf (statementDigest seed s)) t ∧
      2 ^ 22 ≤ t.committedSize ∧ t.committedSize ≤ 2 ^ 28

/-- **Every leaf of at most `2048` raw signatures has a valid execution of the guest**: for every
seed, statement `s` and witness `w` with `NodeRel`, within the deployed limits, with no child and
no blob held directly, at most `2048` raw leanXMSS and leanSPHINCS signatures together and at most
`2048` declared claims and coverage slots, there is a valid execution of the guest on the
statement's digest of committed size in `[2^22, 2^28]`. Proved by
`LeanVM.Guest.Budget.guest_complete_leaf`. -/
abbrev GuestCompleteLeaf : Prop :=
  ∀ (seed : Digest) (s : NodeStatement) (w : NodeWitness),
    NodeRel bytecode seed s w → Limits bytecode s w →
    CapsAgree bytecode seed w → NoZeroChallenge bytecode seed w →
    w.children = [] → (work s w).rawDa = 0 →
    (work s w).rawXmss + (work s w).rawSphincs ≤ 2048 →
    (work s w).declared ≤ 2048 → (work s w).coverage ≤ 2048 →
    ∃ t : Trace guest, ValidExecution guest (publicInputOf (statementDigest seed s)) t ∧
      2 ^ 22 ≤ t.committedSize ∧ t.committedSize ≤ 2 ^ 28

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

/-! ### Honest proofs are children the guest accepts

The statements above assume of each child what `ChildOk` bundles: the hypotheses on the children
of `NodeRel`, `Limits`, `CapsAgree` and `NoZeroChallenge`. `GuestChildComplete` says that the
honest proof of a guest execution meets them. The guest checks a child with the deployed
Keccak-256 and Keccak-f[1600], inside its own execution, so the honest proof is made with them
(`atKeccak`), and what an honest proof can fail by (a proof of work without a nonce within its
fuel, a zero challenge where the guest divides) is bounded in the random-permutation model, for
the same prover and the same check (`verifierNZ`) with `π` in place of Keccak-f[1600]; the
deployed proof meets every hypothesis wherever that check accepts it. -/

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
  /-- Its statement's deferred claim has the bytecode's shape (`NodeRel`). -/
  shaped : c.statement.defer.Shaped bytecode
  /-- The deferring verifier accepts its proof (`NodeRel`). -/
  verifies : verifyDeferred bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true
  /-- Its announced stack log is at least `22` (`Limits.stackLog`). -/
  stackLog : ∀ layout r, announced bytecode c.proof.stream = some (layout, r) →
    Hints.muMin ≤ layout.stackLog
  /-- Its stream has at most `8192` scalars (`Limits.stream`). -/
  stream : c.proof.stream.length ≤ Hints.streamCap
  /-- Its openings agree in the caps (`CapsAgree`). -/
  capsAgree : ∀ b ∈ Limits.queriesOf
      (deferredProgram c.fresh bytecode (statementDigest seed c.statement)) (Hints.childStart seed c),
    Limits.BatchAgrees b.1 b.2
  /-- No zero challenge where the guest divides (`NoZeroChallenge`). -/
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

end LeanVM.Guest.Budget

end

/-! ## The recursion step: the batching in the random-permutation model -/

section

/-!
A node batches its children's claims on the bytecode (`batch`, above): one transcript absorbs
the children's count and every child's public input and claims, squeezes two lambdas per child,
and one sumcheck reduces every child's two claims to one claim at a point, which the node defers.
`BatchSound` bounds the probability that this reduction accepts while a child's claim is false: the recursion step, the guest's batching sound on its own. This is the
batching run outside the circuit, with Keccak-f[1600] = `π`; it does not compose with the guest's
in-circuit statements, whose `KECCAK` instruction computes the deployed Keccak-f[1600], so soundness
across recursion levels does not follow from it.

The batching is written as a program of the verifier's language (`Prog`, `LeanVmVerifier.lean`):
`batchAny M bytecode` reads the count `n < M` as `g^n` then three zeros (`readCount`), `n`
children of `bytecode`'s shapes, each its words then zeros to a whole rate (`readChildren`), then
samples the lambdas, runs the sumcheck's `log₂ |bytecode|` rounds (`roundsProg`), reads the final
value, and accepts if the final claim is the value times the batched weight and the deferred claim
holds of `bytecode` (`batchRest`). It runs from the batching transcript's seed `F(H(label) ‖ 0)`
(`batchVerifier`, `batchSeed` with any `H` and `F`). That the program, run with Keccak-256 and
Keccak-f[1600] on the stream of a node's children and hints, accepts exactly where `batch` defers
a claim that holds is proved in `lean_vm` (`LeanVM.Guest.Batch.runProof_batchAny`).

The experiment is `rpmRun` (`LeanVm.lean`), the adversary's output with the unit statement (the
batching has no statement of its own); the event, `FalseChildren`; `QV = batchQueryBound
bytecode M`. Proved by `LeanVM.Guest.Batch.batch_sound_holds` (`lean_vm`).
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node
open scoped ENNReal

@[expose] public section

/-! ### A child's words -/

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

/-! ### The lambdas and the rounds -/

/-- Sample a pair of lambdas per child. -/
def sampleL : ℕ → Prog (List (E × E))
  | 0 => pure []
  | n + 1 => do
    let a ← Prog.sampleE
    let b ← Prog.sampleE
    let l ← sampleL n
    return (a, b) :: l

/-- **The round polynomial** from the claim before the round and its message `(g(1), g(∞))`:
`g(0) = claim + g(1)`, and `g(x) = (g(∞)·x + g(0) + g(1) + g(∞))·x + g(0)`. -/
def roundPoly (claim : E) (g : E × E) (x : E) : E :=
  (g.2 * x + ((claim + g.1) + g.1 + g.2)) * x + (claim + g.1)

/-- `k` rounds of the batching sumcheck from `claim`: read `g(1)` and `g(∞)`, sample the
challenge, fold. The challenges and the final claim. -/
def roundsProg : E → ℕ → Prog (List E × E)
  | claim, 0 => pure ([], claim)
  | claim, k + 1 => do
    let g1 ← Prog.readE
    let gInf ← Prog.readE
    let r ← Prog.sampleE
    let rest ← roundsProg (roundPoly claim (g1, gInf) r) k
    return (r :: rest.1, rest.2)

/-! ### The program -/

/-- The bytecode's batched claim at the lambdas `lB`. -/
def claimBOf (cs : List ChildClaims) (lB : List (E × E)) : E :=
  sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) cs lB)

/-- The bytecode's batched weight at `y`. -/
def bytecodeWeight (cs : List ChildClaims) (lB : List (E × E)) (y : List E) : E :=
  sumE (List.zipWith (fun c l ↦
    l.1 * eqEval c.fresh.bytecodePoint y + l.2 * eqEval c.carried.bytecodePoint y) cs lB)

open Classical in
/-- **The batching after its children**: the lambdas and the sumcheck, the final value, the
final check, and the deferred claim true of `bytecode`. -/
noncomputable def batchRest (bytecode : List K) (cs : List ChildClaims) : Prog Bool := do
  let l ← sampleL cs.length
  let rb ← roundsProg (claimBOf cs l) (Nat.log2 bytecode.length)
  let bv ← Prog.readE
  Prog.require (rb.2 = bv * bytecodeWeight cs l rb.1 ∧
    DeferredClaim.Holds bytecode ⟨rb.1, bv⟩)
  return true

/-- **The batching of `n` children.** -/
noncomputable def batchProg (bytecode : List K) (n : ℕ) : Prog Bool := do
  let cs ← readChildren (Nat.log2 bytecode.length) n
  batchRest bytecode cs

/-- **The batching as a verifier program**, of fewer than `M` children: the count, then the
batching of that many. -/
noncomputable def batchAny (M : ℕ) (bytecode : List K) : Prog Bool := do
  let n ← readCount M
  batchProg bytecode n

/-- **The batching's verifier**, for a hash function `H` and a permutation `F` in any monad: the
batching transcript's seed `F(H(label) ‖ 0)` (`batchSeed`, with `H` and `F`), then the program
`batchAny M bytecode` on the proof. -/
noncomputable def batchVerifier {m : Type → Type} [Monad m] (H : Bytes → m Digest)
    (F : KState → m KState) (M : ℕ) (bytecode : List K) (proof : Proof) : m Bool := do
  let seed ← F (seedInput (← H batchLabel) (Vector.replicate 4 0))
  runProof H F (batchAny M bytecode) seed proof

/-! ### The event and the bound -/

/-- The count's cells: the generator's power, padded to a whole rate. -/
def headCells (n : ℕ) : List E := padRate [Verifier.gpow n]

/-- A child's cells: its words, padded to a whole rate. -/
def childCells (c : ChildClaims) : List E := padRate c.words

/-- What the batching absorbs before its first challenge. -/
def batchWords (cs : List ChildClaims) : List E := headCells cs.length ++ cs.flatMap childCells

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

end
end LeanVM.Guest.Batch

end

@[expose] public section

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Rpm OracleComp OracleSpec
open scoped ENNReal

/-- **The batching in the random-permutation model.** For a bytecode of power-of-two length and
a bound `M ≤ 2^64 - 1` on the children's count: an adversary of `QA` queries to `π` and `π⁻¹`
outputs a proof; the probability that the batching's verifier, Keccak-256 the sponge over `π` and
Keccak-f[1600] `π`, accepts it while its stream begins with fewer than `M` children of the
bytecode's shapes one of whose claims is false is at most
`(QA + QV + 1) · 2^-191 + 5 (QA + QV)² · 2^-256`, for `QA ≤ 2^128` and the program's query bound
`QV ≤ 2^96`.

This is the batching run outside the circuit, with Keccak-f[1600] = `π`; it does not compose with
the guest's in-circuit statements, whose `KECCAK` instruction computes the deployed Keccak-f[1600],
so soundness across recursion levels does not follow from it. -/
def BatchSound : Prop :=
  ∀ (M : ℕ) (bytecode : List K), bytecode.length = 2 ^ Nat.log2 bytecode.length →
    M ≤ 2 ^ 64 - 1 → ∀ (A : OracleComp PermSpec (Unit × Proof)) (QA : ℕ),
    A.IsTotalQueryBound QA → QA ≤ 2 ^ 128 → batchQueryBound bytecode M ≤ 2 ^ 96 →
    Pr{let z ← rpmRun A fun z ↦ batchVerifier queryH queryF M bytecode z.2}[
      z.2 = true ∧ FalseChildren bytecode M z.1.2] ≤
      (((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ 191 +
        5 * ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM.Guest.Batch

end
