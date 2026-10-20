import LeanerVM.Protocol.EndToEnd.Complete.Small
import LeanerVMTests.Arithmetization.Completeness.Theorem

/-!
# Completeness for small executions, locked

Statement locks of `LeanerVM/Protocol/EndToEnd/Complete/Small.lean`, with their axioms; the
`Trace.Small` constants inhabited by the one-step trace of `PaddedImageRefutation`, which the
theorem gives an admissible witness; each constant of the budget the largest the other two allow;
and the negative case: a `BLAKE2S` table of `2^20` rows has no admissible sizes, whatever the rest.
-/

namespace LeanerVMTests.Protocol.EndToEnd.Complete.Small

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVM.Protocol LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Compile
open LeanerVM.Protocol.Verifier
open LeanerVM.Protocol.EndToEnd.Front LeanerVM.Protocol.EndToEnd.Complete
open LeanerVMTests.Arithmetization.Padding.PaddedImageRefutation
open LeanerVMTests.Arithmetization.Padding.FillBlocks
open LeanerVMTests.Arithmetization.Completeness.Theorem

/-! ## Statement locks -/

example {prog : Program} {input : PublicInput} {t : Trace prog} (hfill : HasFillBlocks prog)
    (hv : ValidExecution prog input t) (hsmall : t.Small) :
    ∃ w s, SatisfiedBy prog input w ∧ Sizes.ofWitness w = some s ∧ s.Admissible prog :=
  exists_admissible_witness hfill hv hsmall

example {prog : Program} {input : PublicInput} {t : Trace prog} {n : ℕ}
    (hfill : HasFillBlocks prog) (hv : ValidExecution prog input t) (hn : t.steps ≤ 2 ^ n)
    (h6 : 6 ≤ n) (hbudget : 8 * 2 ^ t.κ + 2 ^ prog.logSize + 356 * 2 ^ n ≤ 2 ^ maxMu) :
    ∃ t', t'.PaddedFrom t ∧ ValidExecution prog input t' ∧
      ∃ w s, SatisfiedBy prog input w ∧ AssignmentRepresents w t' ∧
        Sizes.ofWitness w = some s ∧ s.Admissible prog :=
  exists_admissible_witness_of_budget hfill hv hn h6 hbudget

example (H : Bytes → Digest) {prog : Program} {input : PublicInput}
    {t : Trace prog} {ρ fuel : ℕ} {proof : Proof}
    (h : honestProofOf H prog input t ρ fuel = some proof) :
    verifyWith (m := Id) H (bytecodeWords prog) (publicDigest input) proof = true :=
  verify_honestProofOf H h

example {prog : Program} {input : PublicInput} {t : Trace prog} {ρ : ℕ}
    (hfill : HasFillBlocks prog) (hv : ValidExecution prog input t) (hsmall : t.Small)
    (hρ : validRate ρ) (H : Bytes → Digest) (fuel : ℕ)
    (hpow : ∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (publicDigest input)).after hist =
          some (.grind bits k) → findNonce H bits cv fuel ≠ none) :
    (honestProofOf H prog input t ρ fuel).isSome :=
  honestProofOf_isSome hfill hv hsmall hρ H fuel hpow

example (prog : Program) (s : Sizes) : (LeanerVM.Protocol.LeanIsa.blocks prog s).total =
    4 * 2 ^ s.logMem + 2 ^ prog.logSize + 2 ^ (8 + s.τ 5) + 15 * 2 ^ s.τ 0 + 15 * 2 ^ s.τ 1 +
      8 * 2 ^ s.τ 2 + 15 * 2 ^ s.τ 3 + 14 * 2 ^ s.τ 4 + 19 * 2 ^ s.τ 5 :=
  blocks_total_eq prog s

/--
info: 'LeanerVM.Protocol.EndToEnd.Complete.exists_admissible_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms exists_admissible_witness

/--
info: 'LeanerVM.Protocol.EndToEnd.Complete.verify_honestProofOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms verify_honestProofOf

/--
info: 'LeanerVM.Protocol.EndToEnd.Complete.complete_of_small' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms complete_of_small

/-! ## An inhabitant -/

/-- The one-step trace of `PaddedImageRefutation` is small: one step, `2^16` words, `2^11` slots. -/
theorem badTrace_small : badTrace.Small := ⟨by decide, by decide, by decide⟩

/-- It has a witness at admissible sizes. -/
theorem badTrace_admissible :
    ∃ w s, SatisfiedBy ladderJumpProg badInput w ∧ Sizes.ofWitness w = some s ∧
      s.Admissible ladderJumpProg :=
  exists_admissible_witness ladderJump_wellFormed.hasFillBlocks badTrace_valid badTrace_small

/-! ## The constants -/

/-- The budget of `Trace.Small` holds. -/
example : 8 * 2 ^ 23 + 2 ^ 23 + 356 * 2 ^ 19 ≤ 2 ^ maxMu := by decide

/-- One more doubling of memory breaks it. -/
example : ¬ 8 * 2 ^ 24 + 2 ^ 23 + 356 * 2 ^ 19 ≤ 2 ^ maxMu := by decide

/-- One more doubling of bytecode breaks it. -/
example : ¬ 8 * 2 ^ 23 + 2 ^ 24 + 356 * 2 ^ 19 ≤ 2 ^ maxMu := by decide

/-- One more doubling of steps breaks it. -/
example : ¬ 8 * 2 ^ 23 + 2 ^ 23 + 356 * 2 ^ 20 ≤ 2 ^ maxMu := by decide

/-- **Past `2^19` steps, no bound of this form holds.** A `BLAKE2S` table of `2^20` rows (a run of
`2^20` `BLAKE2S` steps) is inadmissible for every program and every other size: its Flock region
alone has `2^28` rows. -/
theorem not_admissible_of_blake2s (prog : Program) (s : Sizes) (h : s.τ 5 = 20) :
    ¬ s.Admissible prog := by
  intro hs
  have hμ := (blocks_fits prog s).trans (Nat.pow_le_pow_right (by norm_num) hs.2.2.2.2)
  rw [blocks_total_eq, h] at hμ
  have : 0 < 2 ^ s.logMem := Nat.two_pow_pos _
  have : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
  unfold maxMu at hμ
  omega

end LeanerVMTests.Protocol.EndToEnd.Complete.Small
