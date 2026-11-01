/-
  LeanVM.Guest.EndReplay

  The aggregation guest's soundness for the deployed bytecode with a decoder that replays the
  run: `GuestKnowledge` of `Statement/LeanVmGuest.lean`, the witness read off the frames the run
  entered (`Located.replayFrameV`) through the memory read by the indices of its addresses.
-/

module

public import LeanVM.Guest.EndFinal
public import LeanVM.Guest.Located.Replay

/-!
# The guest's soundness, its decoder replaying the run

`decodeReplay` reads, off a memory `L`, through the index of its `2^κ` addresses
(`Located.readIn`, `Extraction.powIndex`):

* the seed and the statement from `main`'s frame (`fp = 1`): the words of `main`'s certificate's
  cells (`mainValWith`), as `decode` does;
* the witness `B1.Main.decWitV` off `main`'s valuation, the memory and the **replayed** frame map
  (`Located.replayFrameV`): the run from `(g^0, 1)` stepped through the indices, each call given
  the valuation of the first frame at which the run entered its callee, its precondition holding
  and its argument and return cells holding the call's words.

Every test it makes is decided by evaluation: it decides no proposition classically and picks no
witness (`tests/LeanVMTests/Guest/DecodeReplayNoChoice.lean`).

* **`guest_knowledge_replay : GuestKnowledge guest decodeReplay`**: every valid execution of the
  guest on a public input decodes to a statement of that input's digest under the decoded seed,
  and a witness holding it. B2 locates every call of `main` at a frame the run entered
  (`Check.EnteredAt`), so the located relation unfolds along the replayed frame map
  (`Located.unfoldsV_replay`), and B1 applies to it.
* `decodeReplay_eq`: on a memory of fewer than `2^64` words, the decoder is `decodeV`'s reading
  with the replayed frame map in place of `Located.frameV`.
* `decode_binds_replay`: what a consumer learns, as `decode_binds`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Node
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.Binding

@[expose] public section

/-- The words of `main`'s certificate's cells at `fp = 1`, read with `rd` (`Check.valG`). -/
noncomputable def mainValWith (rd : Reader) : Val :=
  fun v ↦ Located.wordWith rd 1 ((certOf 1).locs.getD v.idx 0)

/-- **The guest's decoder, by replay**: through the index of the memory's addresses, the seed and
the statement off `main`'s frame, the witness off `main`'s valuation, the memory and the replayed
frame map. -/
noncomputable def decodeReplay : Decoder := fun {κ} L ↦
  let rd := Located.readIn (Extraction.powIndex κ) L
  let σ := mainValWith rd
  ⟨B1.Main.decSeed σ, B1.Main.decStmt σ rd,
    B1.Main.decWitV σ rd (Located.replayFrameV L) VerifySub.vsPiOf⟩

/-- On a memory of fewer than `2^64` words, the decoder reads `main`'s frame and the memory as
`decodeV` does, with the replayed frame map. -/
theorem decodeReplay_eq {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    decodeReplay L = ⟨B1.Main.decSeed (valG L 1 (certOf 1)),
      B1.Main.decStmt (valG L 1 (certOf 1)) L.read,
      B1.Main.decWitV (valG L 1 (certOf 1)) L.read (Located.replayFrameV L) VerifySub.vsPiOf⟩ := by
  simp only [decodeReplay, Located.readIn_powIndex hκ]
  rfl

/-- **Soundness of the deployed guest, its decoder replaying the run**: every valid execution of
the guest on a public input decodes, from its memory, to a statement of the input's digest under
the decoded seed and a witness holding it. -/
theorem guest_knowledge_replay : GuestKnowledge guest decodeReplay := by
  intro input t hv
  have hκ : t.logMemorySize < 64 := by
    have := hv.1.2.1
    unfold maxLogMem at this
    omega
  show ExplainsInput guest input (decodeReplay t.memory)
  rw [decodeReplay_eq hκ]
  obtain ⟨hb, h0, h1⟩ := mainBodyL_of b2SoundL hv
  have hm : MemOk t.memory.read := ⟨t.logMemorySize, hv.1.1, hv.1.2.1, t.memory, rfl⟩
  exact B1.Main.main_sound_V_of_sub subSoundW bytecode_length t.memory.read hm _ _
    (Located.unfoldsV_replay b2SoundL hv) (Located.rlg_le_rel t.memory) _ _ h0 h1 hb

/-- **What a consumer learns**, the decoder replaying the run: a valid execution of the guest on
the digest of its statement `s₀` under the seed `iv` (`s₀`'s deferred claim of the bytecode's
shape) decodes to `iv` and `s₀`, or its memory and `s₀` give a Keccak-256 collision among the
explicit candidates. -/
theorem decode_binds_replay {input : PublicInput} {t : Execution guest}
    (hv : ValidExecution guest input t) {iv : Digest} {s₀ : NodeStatement}
    (hs₀ : s₀.deferredClaim.HasBytecodeShape bytecode) (hpub : publicDigest input = statementDigest iv s₀) :
    ((decodeReplay t.memory).seed = iv ∧ (decodeReplay t.memory).statement = s₀) ∨
      HasCollision (collisionCandidates (decodeReplay t.memory).seed
        (decodeReplay t.memory).statement iv s₀) := by
  obtain ⟨hd, hrel⟩ := guest_knowledge_replay input t hv
  exact decoded_binds hs₀ hrel.1 hpub hd

end
end LeanVM.Guest.End
