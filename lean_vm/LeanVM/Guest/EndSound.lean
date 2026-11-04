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
* `vsKnown_proved`: `verify_sub`'s `kappa_base` entries below `vsKbBound`, the arms
  `check_opening_terminal` dispatches on (B1-d's `VerifySub.vsKnown_holds`).
* `walkKnown_proved`: the windowed walks' cut obligations (vacuous while no walk certificate
  hands anything on; whir's and ostack's `WinWalk` once checker K's walk obligations land).
* `b2SoundL_of`, `b2SoundL`: checker K's B2 (`b2_step`, `b2_mainL`).
* `soundHyps_of`: what `EndKnow`'s theorems rest on, from `VsKnown` and `main`'s soundness with
  the witness `W` (`Located.MainSoundV bytecode W`).
* `guest_knowledge_sub`, `decode_binds_sub`: the end theorems for the decoder `decodeV piOf`,
  from `verify_sub`'s statement with its proof named by `piOf` (`B1.Main.SubSoundW bytecode piOf`,
  B1-d's); `aggregate_sound_outer_sub` is in `EndRpm.lean`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **`exponent_tables`' relation is the exponent tables** (B1-a's `exponent_tables_holds`). -/
theorem expTablesSound : ExpTablesSound := fun rd q h ↦
  (exponent_tables_holds rd [] [q]).mp h

/-- **`verify_sub`'s `kappa_base`** below `vsKbBound` (B1-d's `VerifySub.vsKnown_holds`;
`coreOf 19` is `Data.core18`). -/
theorem vsKnown_proved : VsKnown := fun L h16 h32 σ hexp h ↦
  VerifySub.vsKnown_holds L h16 h32 σ hexp h

/-- **The walks' obligations**: no callee but `verify_sub` hands anything on at its cuts in the
deployed certificates (`Checked.all_plain`), so `WalkKnown` holds vacuously. -/
theorem walkKnown_proved : WalkKnown := fun j h2 hj h19 hp ↦
  absurd (Checked.all_plain j (by omega) hj (by omega) h19) hp

/-- **B2, proved**, given `verify_sub`'s `kappa_base` bounds and the walks' obligations. -/
theorem b2SoundL_of (hvs : VsKnown) (hwalk : WalkKnown) : B2SoundL :=
  ⟨b2_step fun _ h2 hj ↦ cutsKnown_of hvs hwalk h2 hj, b2_mainL expTablesSound⟩

/-- **B2, proved.** -/
theorem b2SoundL : B2SoundL := b2SoundL_of vsKnown_proved walkKnown_proved

variable {piOf : Reader → Val → FrameMap → Protocol.Compile.Proof}

/-- **Soundness of the deployed guest, its witness named**, from `verify_sub`'s statement. -/
theorem guest_knowledge_sub (hv : B1.Main.SubSoundW bytecode piOf) :
    MemoryGuestKnowledge guestProgram (decodeV piOf) :=
  guest_knowledge_V b2SoundL hv

/-- **What a consumer learns**, from `verify_sub`'s statement. -/
theorem decode_binds_sub (hv : B1.Main.SubSoundW bytecode piOf)
    {input : PublicInput} {t : Execution guestProgram} (hvt : ValidExecution guestProgram input t) {iv : Digest}
    {s₀ : NodeStatement} (hs₀ : s₀.deferredClaim.HasBytecodeShape bytecode)
    (hpub : publicInputDigest input = statementDigest iv s₀) :
    ((decodeV piOf t.memory).seed = iv ∧ (decodeV piOf t.memory).statement = s₀) ∨
      HasCollision (collisionCandidates (decodeV piOf t.memory).seed
        (decodeV piOf t.memory).statement iv s₀) :=
  decode_binds_V b2SoundL hv hvt hs₀ hpub

end
end LeanVM.Guest.End
