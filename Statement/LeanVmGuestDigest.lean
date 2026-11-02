module

public import Statement.LeanVm
public import Statement.LeanXmss
public import Statement.LeanSphincs

/-!
# The leanISA guest program: a node's statement, its digest and the batching program

Reference material for `LeanVmGuest.lean`, which imports it: what a node claims (`NodeStatement`),
the statement's digest under a seed (`statementDigest`, a node's public input, with the bytes it
hashes), and the batching of the children's deferred claims as a program of the verifier's
language (`Batch.nodeBatchingProgram`). Lean defines before use, so these come before the relation
that reads them; a first reading may start at `LeanVmGuest.lean` and look things up here.

Transcribed from leanVM at the pin (`../leanvm-rev`): `crates/rec_aggregation/src/aggregation.rs`
(the statement, its digest, the batching) and `crates/rec_aggregation/guests/lean_ethereum.py`
(the guest program); `aggregation.rs:N` and `lean_ethereum.py:N` are lines of those files at the
pin.
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

/-- The claim a statement defers on the stacked bytecode: its value at a point (`DeferredClaim`,
`aggregation.rs:242-245`), the shape of a proof's claim (`BytecodeClaim`). -/
abbrev DeferredClaim : Type := BytecodeClaim

/-- A node's statement: its claims and its deferred claim. -/
structure NodeStatement where
  /-- Its signature and DA claims. -/
  claims : NodeClaims
  /-- The claim on the bytecode it defers to its parent. -/
  deferredClaim : DeferredClaim

/-- The cells a deferred claim is hashed and absorbed as, and a proof's claim on the bytecode
exported as: the point, then the value (`DeferredClaim::cells`, `aggregation.rs:297-301`; the guest
program's `defer_stmt`, and `verify_sub`'s `defer_out`, `lean_ethereum.py:3324-3329`). -/
def DeferredClaim.cells (claim : DeferredClaim) : List E :=
  claim.bytecodePoint ++ [claim.bytecodeValue]

/-! ## The statement's digest

Each digest is Keccak-256 of its preimage; the preimages are also the inputs of the candidate
collisions (`collisionCandidates`, `LeanVmGuest.lean`). -/

/-- The 16 bytes of a 128-bit value, least significant byte first: a cell's two limbs. -/
def littleEndianBytes16 (value : BitVec 128) : List UInt8 := HashSig.bytesLE 16 value

/-- A claim as the `64` bytes its list hashes: the key's root and parameter, then the message
(`claim_cells`, `aggregation.rs:217-224`). -/
def claimBytes (root parameter : BitVec 128) (message : BitVec 256) : List UInt8 :=
  littleEndianBytes16 root ++ littleEndianBytes16 parameter ++ HashSig.bytesLE 32 message

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

/-- The 24 bytes of a field element, its three limbs. -/
def extensionElementBytes (x : E) : List UInt8 :=
  kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2)

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
    (paddedDeferredClaimCells statement.deferredClaim).flatMap extensionElementBytes

/-- **The statement's digest under `seed`**, a node's public input (`statement_digest`,
`aggregation.rs:331-360`, `lean_ethereum.py:3759-3790`). The cells carry no lengths: the digest
tells two deferred claims apart only at one shape. -/
def statementDigest (seed : Digest) (statement : NodeStatement) : Digest :=
  keccak256 (statementPreimage seed statement)

/-! ## The batching program

The batching of the children's deferred claims (`aggregate_claims`, `lean_ethereum.py:4229-4328`;
`aggregate_deferred_claims`, `aggregation.rs:910-1016`), as a program of the verifier's language
(`Prog`): the count `n` as `g^n` then three zeros, `n` children of the bytecode's shapes, each its
words then zeros to a whole rate (`readChildren`), then one challenge, whose powers are the
lambdas, the sumcheck's `log₂ |bytecode|` rounds (`sumcheckRoundsProgram`) and the final value,
accepted if the final claim is the value times the batched weight and the deferred claim meets a
check (`batchingAfterChildren`); run from the batching transcript's seed (`runBatching`). -/

/-- Words padded with zeros to a whole rate, `rateScalars` words (`pad`,
`aggregation.rs:920-924`; `AGG_CHILD_PAD`). -/
def padToRate (words : List E) : List E :=
  words ++ List.replicate ((rateScalars - words.length % rateScalars) % rateScalars) 0

/-- What a node knows of one child: the child's public input, the claim its proof makes
(`freshClaim`), and the claim its statement defers (`carriedClaim`). -/
structure ChildClaims where
  /-- The child's public input. -/
  publicInput : Digest
  /-- The claim the child's proof makes. -/
  freshClaim : BytecodeClaim
  /-- The claim the child's statement defers. -/
  carriedClaim : DeferredClaim

/-- The words the batching absorbs of a child: its public input's two cells, its proof's claim,
the claim its statement defers (`AGG_CHILD_WORDS`, `lean_ethereum.py:337`). -/
def ChildClaims.words (child : ChildClaims) : List E :=
  [(digestScalars child.publicInput).1, (digestScalars child.publicInput).2] ++
    DeferredClaim.cells child.freshClaim ++ child.carriedClaim.cells

/-- The prover's part of a batching: the sumcheck's rounds and the bytecode's value at its end
(`bc_sumcheck_msgs`, `bc_star_hint`). -/
structure BatchingHints where
  /-- Each round's message `(g(1), g(∞))`. -/
  sumcheckMessages : List (E × E)
  /-- The bytecode's value at the sumcheck's final point. -/
  finalBytecodeValue : E

/-- The batching transcript's label (`RECURSION_AGG_LABEL`, `aggregation.rs:72`). -/
def batchingLabel : List UInt8 := "leanvm/recursion-aggregation/v1".toUTF8.toList

end LeanVM.Node

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

/-- **The lambdas of one challenge `λ`**: child `i`'s pair `(λ^(2i), λ^(2i+1))`, for its fresh
claim and its carried one (`lean_ethereum.py:4291-4305`, `aggregation.rs:940-944`). -/
def lambdaPowers (challenge : E) (childCount : ℕ) : List (E × E) :=
  (List.range childCount).map fun i ↦ (challenge ^ (2 * i), challenge ^ (2 * i + 1))

/-- The bytecode's batched claim at the lambdas. -/
def batchedClaim (children : List ChildClaims) (lambdas : List (E × E)) : E :=
  sumE (List.zipWith (fun child l ↦
    l.1 * child.freshClaim.bytecodeValue + l.2 * child.carriedClaim.bytecodeValue) children lambdas)

/-- The bytecode's batched weight at `point`. -/
def batchedBytecodeWeight (children : List ChildClaims) (lambdas : List (E × E))
    (point : List E) : E :=
  sumE (List.zipWith (fun child l ↦
    l.1 * eqEval child.freshClaim.bytecodePoint point +
      l.2 * eqEval child.carriedClaim.bytecodePoint point) children lambdas)

/-- **The round polynomial** from the claim before the round and its message `(g(1), g(∞))`:
`g(0) = claim + g(1)`, and `g(x) = (g(∞)·x + g(0) + g(1) + g(∞))·x + g(0)`, the degree-2 round
polynomial whose `g(0)` the claim fixes. -/
def sumcheckRoundPolynomial (claim : E) (g : E × E) (x : E) : E :=
  (g.2 * x + ((claim + g.1) + g.1 + g.2)) * x + (claim + g.1)

/-- The words of a child at `bytecodeVariableCount` bytecode coordinates: its public input's two,
its proof's claim, its statement's claim. -/
def childWordCount (bytecodeVariableCount : ℕ) : ℕ :=
  2 + (bytecodeVariableCount + 1) + (bytecodeVariableCount + 1)

/-- The zeros that pad `wordCount` words to a whole rate. -/
def zerosToWholeRate (wordCount : ℕ) : ℕ := (rateScalars - wordCount % rateScalars) % rateScalars

/-- A child read off its words (`ChildClaims.words`); `none` where the public input does not
decode. -/
def parseChild (bytecodeVariableCount : ℕ) (words : List E) : Option ChildClaims := do
  let publicInput ← digestOfScalars (words.getD 0 0, words.getD 1 0)
  let claimWords := words.drop 2
  let carriedWords := claimWords.drop (bytecodeVariableCount + 1)
  return ⟨publicInput,
    ⟨claimWords.take bytecodeVariableCount, claimWords.getD bytecodeVariableCount 0⟩,
    ⟨carriedWords.take bytecodeVariableCount, carriedWords.getD bytecodeVariableCount 0⟩⟩

/-- Read a child: its words, then the zeros to a whole rate. -/
def readChild (bytecodeVariableCount : ℕ) : Prog ChildClaims := do
  let wordCount := childWordCount bytecodeVariableCount
  let words ← Prog.readScalars (wordCount + zerosToWholeRate wordCount)
  Prog.require (words.drop wordCount = List.replicate (zerosToWholeRate wordCount) 0)
  liftOption (parseChild bytecodeVariableCount words)

/-- Read `childCount` children. -/
def readChildren (bytecodeVariableCount : ℕ) : (childCount : ℕ) → Prog (List ChildClaims)
  | 0 => pure []
  | childCount + 1 => do
    let child ← readChild bytecodeVariableCount
    let children ← readChildren bytecodeVariableCount childCount
    return child :: children

/-- `roundCount` rounds of the batching sumcheck from `claim`: read `g(1)` and `g(∞)`, sample the
challenge, fold (`sumcheckRoundPolynomial`). The challenges and the final claim. -/
def sumcheckRoundsProgram : (claim : E) → (roundCount : ℕ) → Prog (List E × E)
  | claim, 0 => pure ([], claim)
  | claim, roundCount + 1 => do
    let g1 ← Prog.readScalar
    let gInfinity ← Prog.readScalar
    let challenge ← Prog.sampleChallenge
    let rest ← sumcheckRoundsProgram (sumcheckRoundPolynomial claim (g1, gInfinity) challenge)
      roundCount
    return (challenge :: rest.1, rest.2)

open Classical in
/-- **The batching after its children**: one challenge and the lambdas of its powers, the
sumcheck's `log₂ |bytecode|` rounds, the final value (`bc_star_hint`, read after the last
challenge: no challenge follows), the final check, and `deferredClaimCheck` of the deferred
claim. -/
noncomputable def batchingAfterChildren (deferredClaimCheck : DeferredClaim → Prop)
    (bytecode : List K) (children : List ChildClaims) : Prog Bool := do
  let challenge ← Prog.sampleChallenge
  let lambdas := lambdaPowers challenge children.length
  let rounds ← sumcheckRoundsProgram (batchedClaim children lambdas) (Nat.log2 bytecode.length)
  let finalValue ← Prog.readScalar
  Prog.require (rounds.2 = finalValue * batchedBytecodeWeight children lambdas rounds.1 ∧
    deferredClaimCheck ⟨rounds.1, finalValue⟩)
  return true

/-- **The batching of `childCount` children.** -/
noncomputable def batchingProgram (deferredClaimCheck : DeferredClaim → Prop) (bytecode : List K)
    (childCount : ℕ) : Prog Bool := do
  let children ← readChildren (Nat.log2 bytecode.length) childCount
  batchingAfterChildren deferredClaimCheck bytecode children

/-- The count's cells: the generator's power, padded to a whole rate. -/
def childCountCells (childCount : ℕ) : List E := padToRate [Verifier.gpow childCount]

/-- A child's cells: its words, padded to a whole rate. -/
def childCells (child : ChildClaims) : List E := padToRate child.words

/-- What the batching absorbs before its first challenge. -/
def cellsBeforeChallenge (children : List ChildClaims) : List E :=
  childCountCells children.length ++ children.flatMap childCells

/-- **The batching of a node's `childCount` children** (`aggregate_claims`): the count's cells,
then the batching of `childCount`, its deferred claim meeting `deferredClaimCheck`. -/
noncomputable def nodeBatchingProgram (deferredClaimCheck : DeferredClaim → Prop)
    (bytecode : List K) (childCount : ℕ) : Prog Bool := do
  let words ← Prog.readScalars rateScalars
  Prog.require (words = childCountCells childCount)
  batchingProgram deferredClaimCheck bytecode childCount

/-- **The batching transcript run**, over a permutation `π` in any monad: from the seed
`π(H(label) ‖ 0)`, `H` Keccak-256 over `π` (`FiatShamirState::from_label`; the guest program bakes
its capacity, `AGG_SEED_*`, `aggregation.rs:2511-2514`), the program on the proof. -/
noncomputable def runBatching {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (program : Prog Bool) (proof : Proof) : m Bool := do
  let seed ← π (seedInput (← keccak256With π batchingLabel) (Vector.replicate 4 0))
  runProof π program seed proof

/-- The stream of a node's batching: the count's and the children's cells, the sumcheck's
messages `(g(1), g(∞))`, the final value. -/
def batchingStream (children : List ChildClaims) (hints : BatchingHints) : List E :=
  cellsBeforeChallenge children ++ hints.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++
    [hints.finalBytecodeValue]

end LeanVM.Guest.Batch

end
