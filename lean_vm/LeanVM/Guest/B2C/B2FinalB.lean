/-
  LeanVM.Guest.B2C.B2FinalB

  B2's completeness at the deployed instance (`B2Final.lean`) under any functional semantics of
  `BLAKE2S`: every compiled function runs by the kernel's completeness checks, so the honest
  memory runs to the end within the counts.
-/

module

public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.B2C.B2B
public import LeanVM.Guest.B2C.FrameAllB
public import LeanVM.Guest.B2C.SemDeployed

/-!
# B2 at the deployed instance under any `BLAKE2S` semantics

`B2Final.lean`'s `b2cB2` and `b2cCount` with `S : BlakeSem` a parameter, functional
(`SemFunctional S`: the frames' shared cells, `frameHoldsB_all`, need it). The checks they rest
on are the kernel's (`Cplw.cplOk_all`, `sitesApart_all_of`), unchanged. What they prove is
`EndCompleteFinal.lean`'s `B2cB2` and `B2cCount` under `S`, stated here (`B2cB2B`, `B2cCountB`,
the counts by `runCountB`).

* `b2cB2B_deployed`, `b2cCountB_deployed`: at `blakeDeployed`, they are `B2cB2` and `B2cCount`;
  with `semFunctional_deployed` (`ShareSoundB.lean`), `b2cB2B` and `b2cCountB` re-derive `b2cB2`
  and `b2cCount` (`b2cB2_of_B`, `b2cCount_of_B`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.End (mainEntry)

@[expose] public section

variable {S : BlakeSem}

variable (S) in
/-- **Checker K's `b2` under `S`** (`B2cB2` under `S`): the honest memory runs from `main`'s entry
to the end. -/
def B2cB2B : Prop :=
  ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAtB S coreProgram fs H C hdr T cert rd [] [] →
      ReachB S guest (honest coreProgram fs H C hdr T) ⟨gpow mainEntry, 1⟩ (Regs.final guest)

variable (S) in
/-- **Checker K's `count` under `S`** (`B2cCount` under `S`): a run of the honest memory to the
end is within the counts. -/
def B2cCountB : Prop :=
  ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAtB S coreProgram fs H C hdr T cert rd [] [] → ∀ n,
      runB S guest (honest coreProgram fs H C hdr T) n Regs.initial = some (Regs.final guest) →
        ∀ op, runCountB S guest (honest coreProgram fs H C hdr T) op n Regs.initial ≤ cnt T op

/-- **Every compiled function runs** under `S` (`B2HypsB.run`), from the kernel's completeness
checks. -/
theorem cplRunB_all : ∀ j, 1 ≤ j → j < nFns → CplRunB S j := cplRunB_of_ok Cplw.cplOk_all

/-- **B2's hypotheses under a functional `S`**: every function runs, and every running
instance's frame holds what the check reads. -/
theorem b2HypsB (hfun : SemFunctional S) : B2HypsB S :=
  ⟨cplRunB_all, frameHoldsB_all hfun (sitesApart_all_of Cplw.cplOk_all)⟩

/-- **Checker K's `b2` under a functional `S`**. -/
theorem b2cB2B (hfun : SemFunctional S) : B2cB2B S := b2B_complete (b2HypsB hfun)

/-- **Checker K's `count` under a functional `S`**. -/
theorem b2cCountB (hfun : SemFunctional S) : B2cCountB S := b2B_count (b2HypsB hfun)

/-! ## At the deployed semantics -/

section Deployed

/-- At the deployed semantics, `B2cB2B` is `EndCompleteFinal.lean`'s `B2cB2`. -/
theorem b2cB2B_deployed : B2cB2B blakeDeployed = B2cB2 := by
  simp only [B2cB2B, B2cB2, honestAtB_deployed, reachB_deployed]

/-- At the deployed semantics, `B2cCountB` is `EndCompleteFinal.lean`'s `B2cCount`. -/
theorem b2cCountB_deployed : B2cCountB blakeDeployed = B2cCount := by
  simp only [B2cCountB, B2cCount, honestAtB_deployed, runB_deployed, runCountB_deployed,
    Trace.count]

/-- `b2cB2B` at the deployed semantics is `B2Final.lean`'s `b2cB2`. -/
theorem b2cB2_of_B : B2cB2 := b2cB2B_deployed ▸ b2cB2B semFunctional_deployed

/-- `b2cCountB` at the deployed semantics is `B2Final.lean`'s `b2cCount`. -/
theorem b2cCount_of_B : B2cCount := b2cCountB_deployed ▸ b2cCountB semFunctional_deployed

end Deployed

end
end LeanVM.Guest.B2C
