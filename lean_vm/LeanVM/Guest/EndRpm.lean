/-
  LeanVM.Guest.EndRpm

  The aggregation guest's theorems that involve an adversary, in the random-permutation model:
  `AggregateSound` of `Statement/LeanVmGuest.lean` for the deployed bytecode and the decoder
  `decode`, and the guest's completeness composed with the protocol's.
-/

import LeanVM.Guest.EndFinal
import LeanVM.Guest.Complete
import LeanVM.Protocol.LeanVMRpm
import Statement.LeanVmGuest
import Common.Transfer
import LeanXmss.Scheme
import Sphincs.Scheme
import Statement.Fast.Schemes
import LeanDa.Scheme
import Statement.Fast.Keccak
import Statement.Fast.CubicExt
import Statement.Fast.FieldWords
import LeanVM.Facts.Verifier

/-!
# The guest in the random-permutation model

The guest's own theorems involve no oracle: `guest_knowledge` (every valid execution decodes),
`decode_binds` and `guest_complete` are about executions and the deployed Keccak. Here they are
composed with the protocol's theorems in the random-permutation model (`Statement/LeanVm.lean`,
`LeanVM/Protocol/LeanVMRpm.lean`):

* `aggregate_knowledge`: in the random-permutation experiment, the verifier accepts a proof of the
  guest from which no execution is extracted (`extractorRpm`, on the adversary's transcript), or
  the extracted one does not decode (`DecodesOn`), with probability at most
  `(Q + 2^14) · 2^-128 + 7 (Q + 2^14)² · 2^-256` for `Q ≤ 2^128`: `KnowledgeSoundness`
  (`knowledgeSoundness_holds`) and `guest_knowledge`.
* `aggregate_sound_outer : AggregateSound guest decode`: with `decode_binds`, an accepted
  aggregate's statement `s`, under the deployed seed and of the guest's shape, is the one the extracted execution decodes, with a witness holding it, or that
  execution's decoding and `s` give an explicit Keccak-256 collision, except with the same
  probability.
* `aggregate_complete_of`: a node within the budget has an execution of the guest whose honest
  proof the verifier rejects, in the random-permutation model, with probability at most
  `completenessError fuel + rpmError (completenessPermCalls fuel)` (`Rpm.completenessRpm`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Guest.Binding
open scoped ENNReal

variable {W : Val → Reader → FrameMap → NodeWitness}

/-- **The aggregate's soundness, its witness named**: in the random-permutation experiment, the
verifier accepts a proof of the guest from which no execution is extracted, or the extracted one
does not decode (`DecodesOn`), with probability at most the bound of `KnowledgeSoundness`. -/
theorem aggregate_knowledge_of (h : SoundHyps W) (A : RpmAdversary) (Q : ℕ)
    (hA : A.IsTotalQueryBound Q) (hQ : Q ≤ 2 ^ 128) :
    Pr{let z ← rpmExperiment A}[z.accepted ∧ z.program = guest ∧
      ¬ ∃ t, extractorRpm z.program z.input z.transcript z.proof = some t ∧
        DecodesOn guest z.input (decodeWith W t.image)] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        7 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  refine le_trans (prEvent_mono _ _ _ ?_) (knowledgeSoundness_holds A Q hA hQ)
  rintro ⟨⟨⟨⟨prog, input⟩, π⟩, b⟩, T⟩ ⟨hb, hprog, hno⟩
  dsimp only [RpmOutcome.program] at hprog
  subst hprog
  refine ⟨hb, ?_⟩
  rintro ⟨t, hx, hv⟩
  exact hno ⟨t, hx, guest_knowledge_of h input t hv⟩

/-- **What the outer verifier's acceptance establishes** (`AggregateSound`), in the
random-permutation model: except with probability the bound of `KnowledgeSoundness`, an accepted
aggregate's statement `s`, under the deployed seed and of the guest's shape,
is the one the execution the extractor reads off the proof and the transcript decodes, with a
witness holding it, or that execution's decoding and `s` give an explicit Keccak-256
collision. -/
theorem aggregate_sound_outer_of (h : SoundHyps W) : AggregateSound guest (decodeWith W) := by
  intro A Q hA hQ
  refine le_trans (prEvent_mono _ _ _ ?_) (aggregate_knowledge_of h A Q hA hQ)
  rintro z ⟨s, hb, hprog, hpub, hs, hno⟩
  refine ⟨hb, hprog, ?_⟩
  rintro ⟨t, hx, hd, hrel⟩
  refine hno ⟨t, hx, ?_⟩
  rcases decoded_binds_of_nodeRel hs hrel hpub hd with ⟨h1, h2⟩ | hc
  · exact Or.inl ⟨h1, h2, h1 ▸ h2 ▸ hrel⟩
  · exact Or.inr hc

/-- **What the outer verifier's acceptance establishes**, from B2 and `verify_sub`'s
statement. -/
theorem aggregate_sound_outer_V {piOf : Reader → Val → FrameMap → Proof} (hb2 : B2SoundL)
    (hv : B1.Main.SubSoundW bytecode piOf) : AggregateSound guest (decodeV piOf) :=
  aggregate_sound_outer_of (soundHyps_of_sub hb2 hv)

/-- **What the outer verifier's acceptance establishes**, from `verify_sub`'s statement. -/
theorem aggregate_sound_outer_sub {piOf : Reader → Val → FrameMap → Proof}
    (hv : B1.Main.SubSoundW bytecode piOf) : AggregateSound guest (decodeV piOf) :=
  aggregate_sound_outer_V b2SoundL hv

/-- **The aggregate's soundness, its witness named**, for the deployed guest and its decoder: in
the random-permutation experiment, the verifier accepts a proof of the guest from which no
execution is extracted, or the extracted one does not decode (`DecodesOn`), with probability at
most `(Q + 2^14) · 2^-128 + 7 (Q + 2^14)² · 2^-256`, for `Q ≤ 2^128`. -/
theorem aggregate_knowledge (A : RpmAdversary) (Q : ℕ) (hA : A.IsTotalQueryBound Q)
    (hQ : Q ≤ 2 ^ 128) :
    Pr{let z ← rpmExperiment A}[z.accepted ∧ z.program = guest ∧
      ¬ ∃ t, extractorRpm z.program z.input z.transcript z.proof = some t ∧
        DecodesOn guest z.input (decode t.image)] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        7 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 :=
  aggregate_knowledge_of (soundHyps_of_sub b2SoundL subSoundW) A Q hA hQ

/-- **What the outer verifier's acceptance establishes** (`AggregateSound`), for the deployed
guest and its decoder, in the random-permutation model: except with probability
`(Q + 2^14) · 2^-128 + 7 (Q + 2^14)² · 2^-256` (for `Q ≤ 2^128`), an accepted aggregate's statement `s`, under
the deployed seed and of the guest's shape, is the one the execution the
extractor reads off the proof and the adversary's transcript (one is extracted) decodes, with a
witness holding it, or that execution's decoding and `s` give an explicit Keccak-256 collision. -/
theorem aggregate_sound_outer : AggregateSound guest decode := aggregate_sound_outer_sub subSoundW

/-- **The guest's completeness in the random-permutation model**: under the hypotheses, there is
an execution of the guest on the statement's digest whose honest proof, at an inverse rate `2^ρ`,
`1 ≤ ρ ≤ 4`, and a fuel of at most `2^64` nonces, the verifier rejects with probability at most
`completenessError fuel + rpmError (completenessPermCalls fuel)` (`Rpm.completenessRpm`). -/
theorem aggregate_complete_of {budget : NodeStatement → NodeWitness → ℕ}
    (h : GuestComplete budget) {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRel bytecode seed s w) (hlim : Limits bytecode s w)
    (hcap : CapsAgree bytecode seed w) (hnz : NoZeroChallenge bytecode seed w) (hbudget : budget s w ≤ 2 ^ 28) :
    ∃ t : Trace guest, ValidExecution guest (publicInputOf (statementDigest seed s)) t ∧
      ∀ ρ fuel, 1 ≤ ρ ∧ ρ ≤ 4 → fuel ≤ 2 ^ 64 →
        Pr{let v ← rpmCompletenessExperiment
            (fun prog input t ρ fuel ↦
              LeanVM.Protocol.EndToEnd.Complete.honestComp prog input t ρ fuel)
            guest (publicInputOf (statementDigest seed s)) t ρ fuel}[v = false] ≤
          completenessError fuel + rpmError (completenessPermCalls fuel) := by
  obtain ⟨t, hv, -, hsize⟩ := h seed s w hrel hlim hcap hnz hbudget
  exact ⟨t, hv, fun _ _ hρ hfuel ↦ Rpm.completenessRpm hv (by omega) hρ hfuel⟩

end LeanVM.Guest.End
