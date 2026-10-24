/-
  LeanVM.Guest.EndSound

  B2 for the deployed bytecode, from the certificates (`Sound.lean`) and B1's two statements about
  the core IR, and the end theorems with what remains of B1 as a hypothesis: `verify_sub`'s
  statement with its proof named (`B1.Main.SubSoundW`).
-/

module

public import LeanVM.Guest.EndKnow
public import LeanVM.Guest.Sound
public import LeanVM.Guest.B1.Bits.Tables
public import LeanVM.Guest.B1.VerifySub.KnownAll

/-!
# B2, proved, and the end theorems from B1's statements

* `expTablesSound`: `exponent_tables`' returns are the exponent tables (B1-a's
  `exponent_tables_holds`).
* `vsKnown_proved`: `verify_sub`'s column logs among `column_selector`'s arms (B1-d's
  `VerifySub.vsKnown_holds`).
* `b2SoundL_of`, `b2SoundL`: checker K's B2 (`b2_step`, `b2_mainL`).
* `soundHyps_of`: what `EndKnow`'s theorems rest on, from `VsKnown` and `main`'s soundness with
  the witness `W` (`Located.MainSoundV bytecode W`).
* `guest_knowledge_sub`, `decode_binds_sub`, `aggregate_sound_outer_sub`: the end theorems for
  the decoder `decodeV piOf`, from `verify_sub`'s statement with its proof named by `piOf`
  (`B1.Main.SubSoundW bytecode piOf`, B1-d's).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **`exponent_tables`' relation is the exponent tables** (B1-a's `exponent_tables_holds`). -/
theorem expTablesSound : ExpTablesSound := fun rd p q h ↦
  (exponent_tables_holds rd [] [p, q]).mp h

/-- **`verify_sub`'s column logs** among `column_selector`'s arms (B1-d's
`VerifySub.vsKnown_holds`; `coreOf 19` is `Data.core18`). -/
theorem vsKnown_proved : VsKnown := fun L h16 h32 σ hexp h ↦
  VerifySub.vsKnown_holds L h16 h32 σ hexp h

/-- **B2, proved**, given `verify_sub`'s column logs. -/
theorem b2SoundL_of (hvs : VsKnown) : B2SoundL := ⟨b2_step hvs, b2_mainL expTablesSound⟩

/-- **B2, proved.** -/
theorem b2SoundL : B2SoundL := b2SoundL_of vsKnown_proved

/-- **What the end theorems rest on**, from `verify_sub`'s column logs and `main`'s soundness with
the witness `W`. -/
theorem soundHyps_of {W : Val → Reader → FrameMap → NodeWitness} (hvs : VsKnown)
    (hm : Located.MainSoundV bytecode W) : SoundHyps W :=
  ⟨b2SoundL_of hvs, hm⟩

variable {piOf : Reader → Val → FrameMap → Proof}

/-- **Soundness of the deployed guest, its witness named**, from `verify_sub`'s statement. -/
theorem guest_knowledge_sub (hv : B1.Main.SubSoundW bytecode piOf) :
    GuestKnowledge guest (decodeV piOf) :=
  guest_knowledge_V b2SoundL hv

/-- **What a consumer learns**, from `verify_sub`'s statement. -/
theorem decode_binds_sub (hv : B1.Main.SubSoundW bytecode piOf)
    {input : PublicInput} {t : Trace guest} (hvt : ValidExecution guest input t) {iv : Digest}
    {s₀ : NodeStatement} (hs₀ : s₀.defer.Shaped bytecode)
    (hpub : publicDigest input = statementDigest iv s₀) :
    ((decodeV piOf t.image).seed = iv ∧ (decodeV piOf t.image).statement = s₀) ∨
      HasCollision (collisionCandidates (decodeV piOf t.image).seed
        (decodeV piOf t.image).statement iv s₀) :=
  decode_binds_V b2SoundL hv hvt hs₀ hpub

/-- **What the outer verifier's acceptance establishes**, from `verify_sub`'s statement. -/
theorem aggregate_sound_outer_sub (hv : B1.Main.SubSoundW bytecode piOf) :
    AggregateSound guest (decodeV piOf) :=
  aggregate_sound_outer_V b2SoundL hv

end
end LeanVM.Guest.End
