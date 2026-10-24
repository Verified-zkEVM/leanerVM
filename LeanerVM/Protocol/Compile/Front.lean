/-
  LeanerVM.Protocol.Compile.Front

  The front of the executable verifier's algebra at leanVM's instance is the front of the oracle
  protocol: on transcripts of the four front phases of `leanVmPhases` whose checks pass in
  sequence, the algebra's bus, table, public-input and Flock steps accept their wires, with the
  oracle verifiers' outputs.
-/

module

public import LeanerVM.Protocol.Compile.Flock
public import LeanerVM.Protocol.Piop

/-!
# The front phases at leanVM's instance

The phases of `leanVmPhases` before the opening are front phases: each is a check and a verdict
on its statement and its transcript. The executable verifier's algebra (`Verify.algebra`) runs
four steps on the wire before the opening's claim: `leanVmBus`, `tableStep`, `pubStep` and
`flockStep` with the BLAKE2s circuit's walk. On transcripts whose checks pass in sequence, each
step accepts the transcript's wire with the oracle verifier's output (`leanVmFront_of_checks`),
from the phase lemmas `busStep_busWireOf`, `tableStep_tableWireOf`, `pubStep_eq` and
`flockStep_flockWireOf`. The four phases are the front slots of `leanVmPhases`, the Flock slot at
leanVM's instance being the phase on the instance's region (`flockPhase_leanVm`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanIsa ProtocolSpec Verify

@[expose] public section

namespace Compile

variable (prog : Program) (sz : Sizes)

/-- At leanVM's instance the Flock slot of `leanVmPhases` is the phase on the instance's region. -/
theorem flockPhase_leanVm :
    flockPhase (leanVm prog sz) =
      flockPhaseSome (leanVm prog sz) (flockRegion prog sz Blake2sFlock.blake2sFlockSpec) rfl :=
  rfl

/-- **The front of the algebra is the oracle protocol's front** at leanVM's instance: on
transcripts of the bus phase, the table sumcheck, the public input and the Flock phase (the four
front slots of `leanVmPhases`) whose checks pass in sequence, the algebra's four steps accept the
transcripts' wires, with the oracle verifiers' output. -/
theorem leanVmFront_of_checks (input : PublicInput)
    (t₂ : (busSpec (leanVm prog sz)).FullTranscript)
    (t₃ : (tableSpec (leanVm prog sz)).FullTranscript) (t₄ : pubSpec.FullTranscript)
    (t₅ : (flockSpecOf (flockRegion prog sz Blake2sFlock.blake2sFlockSpec).kBatch).FullTranscript)
    (h₂ : (busPhase (leanVm prog sz) (leanIsa_conditions _ prog sz)).front.check input t₂ = true)
    (h₃ : (TableSumcheck.tableSumcheck (leanVm prog sz)).front.check
      ((busPhase (leanVm prog sz) (leanIsa_conditions _ prog sz)).front.out input t₂) t₃ = true)
    (h₄ : (deployedPublicInputPhase (leanVm prog sz)).front.check
      ((TableSumcheck.tableSumcheck (leanVm prog sz)).front.out
        ((busPhase (leanVm prog sz) (leanIsa_conditions _ prog sz)).front.out input t₂) t₃) t₄ =
      true)
    (h₅ : (flockPhaseSome (leanVm prog sz) (flockRegion prog sz Blake2sFlock.blake2sFlockSpec)
      rfl).front.check ((deployedPublicInputPhase (leanVm prog sz)).front.out
        ((TableSumcheck.tableSumcheck (leanVm prog sz)).front.out
          ((busPhase (leanVm prog sz) (leanIsa_conditions _ prog sz)).front.out input t₂) t₃)
        t₄) t₅ = true) :
    ((((leanVmBus prog sz input (busWireOf (leanVm prog sz) t₂)).bind fun b ↦
        tableStep (leanVm prog sz) b (tableWireOf (leanVm prog sz) t₃)).bind fun t ↦
        pubStep (leanVm prog sz) t (pubWireOf t₄)).bind fun p ↦
        flockStep (leanVm prog sz) (flockRegion prog sz Blake2sFlock.blake2sFlockSpec) rfl
          blake2sRows p
          (flockWireOf (flockRegion prog sz Blake2sFlock.blake2sFlockSpec).kBatch t₅)) =
      some ((flockPhaseSome (leanVm prog sz) (flockRegion prog sz Blake2sFlock.blake2sFlockSpec)
        rfl).front.out ((deployedPublicInputPhase (leanVm prog sz)).front.out
          ((TableSumcheck.tableSumcheck (leanVm prog sz)).front.out
            ((busPhase (leanVm prog sz) (leanIsa_conditions _ prog sz)).front.out input t₂) t₃)
          t₄) t₅) := by
  rw [leanVmBus_eq_busStep, busStep_busWireOf _ _ _ t₂ h₂, Option.bind_some,
    tableStep_tableWireOf _ _ t₃ h₃, Option.bind_some, pubStep_eq, pubTr_pubWireOf,
    Component.Front.run_of_check _ h₄, Option.bind_some,
    flockStep_flockWireOf (leanVm prog sz) (flockRegion prog sz Blake2sFlock.blake2sFlockSpec) rfl
      blake2sRows (blake2sRows_eq_region prog sz) _ t₅ h₅]

end Compile

end
end LeanerVM.Protocol
