/-
  LeanVM.Guest.EndFinal

  The aggregation guest's soundness for the deployed bytecode, with nothing assumed: the decoder
  `decode` and the statements `GuestKnowledge` and `AggregateSound` of `LeanVM/Spec/Guest.lean`.
-/

module

public import LeanVM.Guest.EndSound
public import LeanVM.Guest.B1.VerifySub.Sound

/-!
# The guest's soundness

`decode` reads, off a memory `L`, the seed and the statement from `main`'s frame (`fp = 1`) and
the witness `B1.Main.decWitV` off `main`'s valuation, the memory and the memory's frame map
(`Located.frameV`: each call's valuation is its frame's, the first frame of the memory at which
the callee's code holds on the call's words): each leanXMSS and leanSPHINCS signature off the
frame of its check, the DA matrix off `da_verify`'s and its callees' frames, each child's proof
off its `verify_sub` frame and the memory (`VerifySub.vsPiOf`: the stream words `verify_sub`
reads, the openings `open_stacked`'s queries hash), the batching's hints off `aggregate_claims`'
frame and the memory. It chooses nothing (`tests/LeanVMTests/Guest/DecodeNoChoice.lean`). It
computes no hash and runs no verifier of its own; it finds each call's frame as the first of the
memory's `2^κ` frames at which the guest's own code for the callee holds on the call's words (a
classical test of the guest's semantics, which includes its in-circuit checks), and reads the
witness there.

* `guest_knowledge : GuestKnowledge guest decode`: every valid execution of the guest on a public
  input decodes to a statement of that input's digest under the decoded seed, and a witness
  holding it (`NodeRel`).
* `aggregate_sound_outer : AggregateSound guest decode`: in the random-oracle experiment, the
  verifier accepts a proof of the guest on the digest of a statement `s` under the deployed seed,
  `s` passing the outer verifier's other checks, while no execution is extracted from the proof
  and the adversary's answers, or the extracted one does not decode to the deployed seed, `s` and
  a witness holding it, nor give a Keccak-256 collision among `collisionCandidates`, with
  probability at most `soundnessError Q`.
* `decode_binds`: a consumer whose statement `s₀` (its deferred claim of the bytecode's shape) has,
  under the seed
  `iv`, the public input's digest learns that the decoded seed and statement are `iv` and `s₀`,
  or holds an explicit Keccak-256 collision.

They rest on B2 (`b2SoundL`: the kernel-checked certificates and `VsKnown`) and B1
(`B1.Main.main_sound_V_of_sub` with `VerifySub.verify_sub_sound_w`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open scoped ENNReal

@[expose] public section

/-- **The guest's decoder**: the seed and the statement off `main`'s frame, the witness off the
frames of the functions that checked it. -/
noncomputable def decode : Decoder := decodeV VerifySub.vsPiOf

/-- `verify_sub`'s statement, its proof `VerifySub.vsPiOf`, for the guest's bytecode. -/
theorem subSoundW : B1.Main.SubSoundW bytecode VerifySub.vsPiOf :=
  VerifySub.verify_sub_sound_w bytecode

/-- **Soundness of the deployed guest, its witness named**: every valid execution of the guest on
a public input decodes, from its memory, to a statement of the input's digest under the decoded
seed and a witness holding it. -/
theorem guest_knowledge : GuestKnowledge guest decode := guest_knowledge_sub subSoundW

/-- **The aggregate's soundness against the random oracle, its witness named**: the verifier
accepts a proof of the guest from which no execution is extracted, or the extracted one does not
decode (`DecodesOn`), with probability at most `soundnessError Q`. -/
theorem aggregate_knowledge (A : Adversary) (Q : ℕ) (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[z.accepted ∧ z.program = guest ∧
      ¬ ∃ t, extractor z.program z.input z.adversaryCache z.proof = some t ∧
        DecodesOn guest z.input (decode t.image)] ≤ soundnessError Q :=
  aggregate_knowledge_of (soundHyps_of_sub b2SoundL subSoundW) A Q hA

/-- **What a consumer learns**: a valid execution of the guest on the digest of its statement
`s₀` under the seed `iv` (`s₀`'s deferred claim of the bytecode's shape: `bytecode`'s `23`
coordinates, which the outer verifier's check that it holds implies) decodes to
`iv` and `s₀`, or its memory and `s₀` give a Keccak-256 collision among the explicit
candidates. -/
theorem decode_binds {input : PublicInput} {t : Trace guest} (hv : ValidExecution guest input t)
    {iv : Digest} {s₀ : NodeStatement} (hs₀ : s₀.defer.Shaped bytecode)
    (hpub : publicDigest input = statementDigest iv s₀) :
    ((decode t.image).seed = iv ∧ (decode t.image).statement = s₀) ∨
      HasCollision (collisionCandidates (decode t.image).seed (decode t.image).statement iv s₀) :=
  decode_binds_sub subSoundW hv hs₀ hpub

/-- **What the outer verifier's acceptance establishes** (`AggregateSound`): except with
probability `soundnessError Q`, an accepted aggregate's statement `s`, under the deployed seed
and passing the outer verifier's other checks, is the one the execution the extractor reads off
the proof (one is extracted) decodes, with a witness holding it, or that execution's decoding and
`s` give an
explicit Keccak-256 collision. -/
theorem aggregate_sound_outer : AggregateSound guest decode := aggregate_sound_outer_sub subSoundW

/-- **Soundness, the existential form**: a valid execution of the guest on `input` gives a seed and
a statement of the input's digest, of the guest's shape, that a witness holds (`NodeSpec`). -/
theorem guest_sound (input : PublicInput) (t : Trace guest) (hv : ValidExecution guest input t) :
    ∃ seed s, statementDigest seed s = publicDigest input ∧ s.defer.Shaped bytecode ∧
      NodeSpec bytecode seed s :=
  guest_sound_of (soundHyps_of_sub b2SoundL subSoundW) input t hv

end
end LeanVM.Guest.End
