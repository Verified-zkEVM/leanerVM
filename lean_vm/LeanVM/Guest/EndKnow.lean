/-
  LeanVM.Guest.EndKnow

  The aggregation guest's soundness, its witness named: the decoder that reads a statement and
  its witness off a valid execution's memory, and the theorems `GuestKnowledge` and
  `AggregateKnowledge` of `LeanVM/Spec/Guest.lean` for the deployed bytecode.
-/

module

public import LeanVM.Guest.EndLoc
public import LeanVM.Guest.Located.Main
public import LeanVM.Guest.Located.VerifySub
public import LeanVM.Guest.Binding
public import LeanVM.Spec.Guest

/-!
# The guest's witness, named

`guest_sound` concludes that some seed, statement and witness exist; `guest_knowledge` names them.
The decoder `decode` reads, off a memory `L`:

* the seed, the statement and the children's statements, fresh claims and batching from `main`'s
  frame (`fp = 1`, the words of `main`'s certificate's cells: `B1.Main.decSeed`, `decStmt`,
  `decWit`);
* each leanXMSS and leanSPHINCS signature, blob matrix and child proof from the frame of the
  function that checked it, the frame at which that function's code holds on the call's words
  (`Located.frameOf`; `Located.xmssWit`, `sphincsWit`, `wDaL`,
  `wVsL`), and the batching's hints from `aggregate_claims`' frame (`Located.wAL`).

`guest_knowledge`: every valid execution of the guest on a public input decodes to a statement of
that input's digest under the decoded seed and a witness holding it (`NodeRel`). B2 gives `main`'s
body at its frame with every call located (`mainBodyL_of`); B1 gives `main`'s meaning over the
decoded witness (`B1.Main.main_sound_w`), each callee's witness the one its located frame holds.

`aggregate_knowledge`: in the random-oracle experiment, the verifier accepts a proof of the guest
whose extracted execution (`LeanVM.extract`) does not decode so with probability at most
`soundnessError Q`.

`decode_binds`: a consumer whose own statement `s₀` (its deferred claim true) has, under the
deployed seed `iv`, the public input's digest learns that the decoded seed and statement are `iv`
and `s₀`, or holds an explicit BLAKE2s collision (`collisionCandidates`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.EndToEnd
open LeanVM.Guest.Binding
open scoped ENNReal

@[expose] public section

/-- **The guest's decoder**: the seed, the statement and the witness `main`'s frame and the
frames of its callees hold. -/
noncomputable def decode : Decoder := fun {_} L ↦
  let σ := valG L 1 (certOf 1)
  (B1.Main.decSeed σ, B1.Main.decStmt σ L.read,
    B1.Main.decWit σ L.read (Located.xmssWit L) (Located.sphincsWit L) (Located.wDaL L)
      (fun args ↦ Located.wVsL L args []) (Located.wAL L))

/-- A located call is its callee's body at a valuation (`B1.Main.Unfolds`). -/
theorem unfolds_RL {κ : ℕ} (L : MemImage κ) : B1.Main.Unfolds L.read (RL coreProgram L certByName) :=
  fun f args rets h ↦ by
    obtain ⟨fn, fp, hf, -, hp, hb⟩ := (relL_iff coreProgram f args rets).mp h
    exact ⟨fn, _, hf, hp, hb⟩

/-- **Soundness of the deployed guest, its witness named**: every valid execution of the guest on
a public input decodes, from its memory, to a statement of the input's digest under the decoded
seed and a witness holding it. -/
theorem guest_knowledge : GuestKnowledge guest decode := by
  intro input t hv
  obtain ⟨hb, h0, h1⟩ := mainBodyL_of hv
  have h16 : 16 ≤ t.κ := hv.1.1
  have h32 : t.κ ≤ 32 := hv.1.2.1
  have hm : B1.Main.MemOk t.image.read := ⟨t.κ, h16, h32, t.image, rfl⟩
  have H := Located.calleesW_located hm (wV := fun args ↦ Located.wVsL t.image args [])
    (fun _ _ _ _ _ _ _ ht h ↦ by
      obtain ⟨pi, iv, fresh, h1, h2, h3, h4, h5⟩ := Located.vsWit_out h32 (by omega) ht h
      exact ⟨pi, iv, fresh, h1, h2, h3, h4, h5⟩)
  exact B1.Main.main_sound_w bytecode_length hm (unfolds_RL t.image) H h0 h1 hb

/-- **The aggregate's soundness against the random oracle, its witness named**. -/
theorem aggregate_knowledge : AggregateKnowledge guest LeanVM.extract decode := by
  intro A Q hA
  refine le_trans (prEvent_mono _ _ _ ?_) (LeanVM.knowledgeSoundness hA)
  rintro ⟨⟨⟨⟨prog, input⟩, π⟩, b⟩, c⟩ ⟨hb, hprog, hno⟩
  dsimp only at hb hprog hno
  subst hprog
  refine ⟨hb, guest_sentinelSafe, ?_⟩
  rintro ⟨t, hx, hv⟩
  exact hno ⟨t, hx, guest_knowledge input t hv⟩

/-- **What a consumer learns**: a decoded execution of the guest on the digest of its statement
`s₀` under the deployed seed `iv` (`s₀`'s deferred claim true, as the outer verifier checks)
decodes to `iv` and `s₀`, or its memory and `s₀` give a BLAKE2s collision among the explicit
candidates. -/
theorem decode_binds {input : PublicInput} {t : Trace guest} (hv : ValidExecution guest input t)
    {iv : Digest} {s₀ : NodeStatement} (hs₀ : s₀.defer.Holds bytecode)
    (hpub : publicDigest input = statementDigest iv s₀) :
    ((decode t.image).1 = iv ∧ (decode t.image).2.1 = s₀) ∨
      ∃ p ∈ collisionCandidates (decode t.image).1 (decode t.image).2.1 iv s₀,
        p.1 ≠ p.2 ∧ blake2sBytes p.1 = blake2sBytes p.2 := by
  obtain ⟨hd, hrel⟩ := guest_knowledge input t hv
  exact decoded_binds_of_nodeRel hs₀ hrel hpub hd

/-- **What the outer verifier's acceptance establishes** (`AggregateSound`): except with
probability `soundnessError Q`, an accepted aggregate's statement `s`, under the deployed seed and
its deferred claim true, is the one the execution the proof commits to decodes, with a witness
holding it, or that execution's decoding and `s` give an explicit BLAKE2s collision. -/
theorem aggregate_sound_outer : AggregateSound guest LeanVM.extract decode := by
  intro A Q hA
  refine le_trans (prEvent_mono _ _ _ ?_) (aggregate_knowledge A Q hA)
  rintro z ⟨hb, hprog, s, hpub, hs, -, hno⟩
  refine ⟨hb, hprog, ?_⟩
  rintro ⟨t, hx, hd, hrel⟩
  refine hno ⟨t, hx, ?_⟩
  rcases decoded_binds_of_nodeRel hs hrel hpub hd with ⟨h1, h2⟩ | hc
  · exact Or.inl ⟨h1, h2, h1 ▸ h2 ▸ hrel⟩
  · exact Or.inr hc

end
end LeanVM.Guest.End
