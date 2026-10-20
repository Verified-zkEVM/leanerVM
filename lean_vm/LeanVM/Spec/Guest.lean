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
* `AggregateSound guest extract decode`, what a consumer learns: in the random-oracle experiment,
  the verifier accepts a proof of `guest` on the digest of a statement `s` under the deployed seed,
  `s` passing the outer verifier's other checks (`OuterChecks`), while the execution `extract`
  reads off the proof does not explain `s` (`Explains`: decode to the deployed seed, `s` and a
  witness holding it, or give a BLAKE2s collision among `collisionCandidates`), with probability
  at most `soundnessError Q`.

Both hold of any decoder that happens to output valid witnesses; their content is in the decoder
the theorems name (`LeanVM.Guest.End.decode`), which reads every component off the memory: the
statement from `main`'s frame, each signature, matrix and child proof from the frame of the
function that checked it, the first frame of the memory at which that function's code holds on
the call's words. The decoder chooses nothing and verifies nothing. The seed is the guest's hint:
the statement's digest binds it, so a consumer comparing the digest with its own statement's under
the deployed seed learns both, unless it holds a BLAKE2s collision.
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open scoped ENNReal

@[expose] public section

/-! ## The bytes each digest hashes, and the candidate collisions -/

/-- The deferred claim's cells, an odd count paired with a zero cell. -/
def paddedCells (c : DeferredClaim) : List E :=
  c.cells ++ if c.cells.length % 2 = 1 then [0] else []

/-- The bytes of a statement under `seed`, before the zero fill. -/
def statementBytes (seed : Digest) (s : NodeStatement) : List UInt8 :=
  digestBytes seed ++ digestBytes (signersDigest s.claims.xmss s.claims.sphincs) ++
    digestBytes (daListDigest s.claims.da) ++ (paddedCells s.defer).flatMap eBytes

/-- The bytes `statementDigest seed s` hashes: zero-filled to whole 64-byte blocks. -/
def statementPreimage (seed : Digest) (s : NodeStatement) : List UInt8 :=
  statementBytes seed s ++
    List.replicate ((64 - (statementBytes seed s).length % 64) % 64) 0

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

/-- The guest's deployed seed: its Fiat-Shamir IV. -/
abbrev deployedSeed (guest : Program) : Digest := fiatShamirIv (bytecodeWords guest)

/-- **What the outer verifier checks of a statement besides its proof** (`verifyAggregate`): every
DA claim's vector digest is its root's, and the deferred claim holds of the guest's bytecode. -/
def OuterChecks (guest : Program) (s : NodeStatement) : Prop :=
  (∀ c ∈ s.claims.da, Da.toBytes c.2 = Da.vectorDigestOf c.1) ∧ s.defer.Holds (bytecodeWords guest)

/-- **A collision**: a pair of different inputs with the same BLAKE2s digest, among `pairs`. -/
def HasCollision (pairs : List (List UInt8 × List UInt8)) : Prop :=
  ∃ p ∈ pairs, p.1 ≠ p.2 ∧ blake2sBytes p.1 = blake2sBytes p.2

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
holding `s`; or the decoded seed and statement, with the deployed seed and `s`, give a BLAKE2s
collision among the candidates. -/
def Explains (guest : Program) (s : NodeStatement) (d : Decoded) : Prop :=
  (d.seed = deployedSeed guest ∧ d.statement = s ∧
      NodeRel (bytecodeWords guest) (deployedSeed guest) s d.witness) ∨
    HasCollision (collisionCandidates d.seed d.statement (deployedSeed guest) s)

/-- **The outer verifier's acceptance, explained.** The adversary outputs a proof. The event: the
verifier accepts it as a proof of `guest` on the digest, under the deployed seed, of a statement
`s` that passes the outer verifier's other checks, and yet the execution `extract` reads off the
oracle's answers and the proof does not explain `s`. Its probability is at most
`soundnessError Q`. -/
def AggregateSound (guest : Program) (extract : Extractor) (decode : Decoder) : Prop :=
  ∀ (A : Adversary) (Q : ℕ), A.IsTotalQueryBound Q →
    Pr{let z ← experiment A}[
      let prog := z.1.1.1.1
      let input := z.1.1.1.2
      ∃ s : NodeStatement, z.1.2 = true ∧ prog = guest ∧
        publicDigest input = statementDigest (deployedSeed guest) s ∧ OuterChecks guest s ∧
        ¬ ∃ t, extract prog input z.2 z.1.1.2 = some t ∧ Explains guest s (decode t.image)] ≤
      soundnessError Q

end
end LeanVM.Node
