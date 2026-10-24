/-
  LeanVM.Spec.Guest

  What a proof of the aggregation guest establishes, its witness named: the statement and the
  witness are read off the execution's memory.
-/

module

public import LeanVM.Spec.Node

/-!
# The aggregation guest, its witness named

`NodeSpec` (`Node.lean`) is the existential `∃ w, NodeRel …`. A hash-based witness (a signature, a
child's proof, a blob matrix) exists for nearly every claim, so "some witness holds the statement"
says little. What a valid execution of the guest establishes is more: its memory holds the
witness. A **decoder** reads a seed, a statement and a witness off a memory (`Decoder`,
`Decoded`), and the guest's soundness is stated for it:

* `GuestKnowledge guest decode`: every valid execution of `guest` on a public input decodes to a
  statement of that input's digest under the decoded seed, and a witness holding it;
* `AggregateSound guest decode` (`Aggregate.lean`), what a consumer learns, in the
  random-permutation model of `Rpm.lean`: the verifier accepts a proof of `guest` on the digest of
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

/-! ## The bytes each digest hashes, and the candidate collisions -/

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
  claims.flatMap fun c ↦ digestBytes c.1 ++ digestBytes c.2

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

/-! ## Decoders -/

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

/-! ## What a proof of the guest establishes -/

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
