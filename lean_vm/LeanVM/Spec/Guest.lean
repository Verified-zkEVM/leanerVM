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
says little. What a valid execution of the guest establishes is more: its memory holds the witness.
A **decoder** reads a seed, a statement and a witness off a memory (`Decoder`), and the guest's
soundness is stated for it:

* `GuestKnowledge guest decode`: every valid execution of `guest` on a public input decodes, from its
  memory, to a statement of that input's digest under the decoded seed, and to a witness holding it;
* `AggregateKnowledge guest extract decode`: in the random-oracle experiment, the verifier accepts a
  proof of `guest` while the execution `extract` reads off the oracle's answers and the proof does
  not decode so, with probability at most `soundnessError Q`;
* `AggregateSound guest extract decode`, the consumer's statement: the outer verifier's checks
  (the proof on the digest of `s` under the deployed seed, `s`'s deferred claim, its DA digests)
  pass while the extracted execution does not decode to the deployed seed, `s` and a witness
  holding it, nor give with `s` a BLAKE2s collision among `collisionCandidates`, with probability
  at most `soundnessError Q`.

Both propositions hold of any decoder that happens to output valid witnesses; their content is in the
decoder the theorems name (`LeanVM.Guest.End.decode`), which reads every component off the memory:
the statement from `main`'s frame, each signature, matrix and child proof from the frame of the
function that checked it: the first frame of the memory at which that function's code holds on the
call's words. The decoder verifies nothing itself. The seed is the guest's hint: the
statement's digest binds it, and a consumer comparing the digest with its own statement's under the
deployed seed learns both, unless it holds a BLAKE2s collision.
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

/-! ## Decoders and knowledge -/

/-- A decoder: from a memory, a seed, a statement and a witness. -/
abbrev Decoder : Type := ∀ {κ : ℕ}, MemImage κ → Digest × NodeStatement × NodeWitness

/-- **What the execution `t` of `guest` on `input` decodes to**: a statement of the input's digest
under the decoded seed, and a witness holding it for the guest's bytecode. -/
def DecodesOn (guest : Program) (decode : Decoder) (input : PublicInput) (t : Trace guest) : Prop :=
  statementDigest (decode t.image).1 (decode t.image).2.1 = publicDigest input ∧
    NodeRel (bytecodeWords guest) (decode t.image).1 (decode t.image).2.1 (decode t.image).2.2

/-- **Knowledge soundness of the guest, its witness named**: every valid execution decodes. -/
def GuestKnowledge (guest : Program) (decode : Decoder) : Prop :=
  ∀ input (t : Trace guest), ValidExecution guest input t → DecodesOn guest decode input t

/-- **In the random-oracle model**: the adversary chooses a statement and a proof; the verifier
accepts, the program is the guest, and the execution `extract` reads off the oracle's answers and
the proof does not decode, with probability at most `soundnessError Q`. -/
def AggregateKnowledge (guest : Program) (extract : Extractor) (decode : Decoder) : Prop :=
  ∀ (A : Adversary) (Q : ℕ), A.IsTotalQueryBound Q →
    Pr{let z ← experiment A}[z.1.2 = true ∧ z.1.1.1.1 = guest ∧
      ¬ ∃ t, extract z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2 = some t ∧
        statementDigest (decode t.image).1 (decode t.image).2.1 = publicDigest z.1.1.1.2 ∧
        NodeRel (bytecodeWords guest) (decode t.image).1 (decode t.image).2.1
          (decode t.image).2.2] ≤ soundnessError Q

/-- **What the outer verifier's acceptance establishes, its witness named.** The adversary outputs
a proof of `guest`. The event: the verifier accepts it on its public input, which is the digest,
under the deployed seed `fiatShamirIv`, of a statement `s` whose deferred claim holds and whose DA
claims' vector digests are their roots' (what `verifyAggregate` checks beside the proof); and yet
the execution `extract` reads off the oracle's answers and the proof neither decodes to the
deployed seed, `s` and a witness holding it, nor gives, with `s`, a BLAKE2s collision among the
candidates. Its probability is at most `soundnessError Q`. -/
def AggregateSound (guest : Program) (extract : Extractor) (decode : Decoder) : Prop :=
  ∀ (A : Adversary) (Q : ℕ), A.IsTotalQueryBound Q →
    Pr{let z ← experiment A}[z.1.2 = true ∧ z.1.1.1.1 = guest ∧
      ∃ s : NodeStatement,
        publicDigest z.1.1.1.2 = statementDigest (fiatShamirIv (bytecodeWords guest)) s ∧
        s.defer.Holds (bytecodeWords guest) ∧
        (∀ c ∈ s.claims.da, Da.toBytes c.2 = Da.vectorDigestOf c.1) ∧
        ¬ ∃ t, extract z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2 = some t ∧
          (((decode t.image).1 = fiatShamirIv (bytecodeWords guest) ∧ (decode t.image).2.1 = s ∧
              NodeRel (bytecodeWords guest) (fiatShamirIv (bytecodeWords guest)) s
                (decode t.image).2.2) ∨
            ∃ p ∈ collisionCandidates (decode t.image).1 (decode t.image).2.1
                (fiatShamirIv (bytecodeWords guest)) s,
              p.1 ≠ p.2 ∧ blake2sBytes p.1 = blake2sBytes p.2)] ≤ soundnessError Q

end
end LeanVM.Node
