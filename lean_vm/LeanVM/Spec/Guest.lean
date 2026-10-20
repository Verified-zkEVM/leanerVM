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
  not decode so, with probability at most `soundnessError Q`.

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

end
end LeanVM.Node
