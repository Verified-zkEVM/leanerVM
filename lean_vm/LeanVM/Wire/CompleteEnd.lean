/-
  LeanVM.Wire.CompleteEnd

  The end theorem of completeness on the wire: `LeanVM.Wire.completenessOnBytes_holds`.
-/

import LeanVM.Prover.End
import LeanVM.Wire.Complete
import LeanVM.Wire.Honest

/-!
# Completeness on the wire holds

`completenessOnBytes_of` (`LeanVM/Wire/Complete.lean`) at the honest prover's facts
(`proveWithHash_wireDecodable`, `proveWithHash_climbInputsIn`, `LeanVM/Wire/Honest.lean`) and the
structured completeness with the two calls (`completenessWithHash_holds`,
`LeanVM/Prover/End.lean`): the honest prover's bytes are rejected by the verifier on bytes with
probability at most `2^-256`.
-/

namespace LeanVM.Wire

/-- What completeness on the wire needs of the honest prover holds. -/
theorem honestWireFacts : HonestWireFacts :=
  ⟨fun _ _ _ _ _ _ _ _ hp ↦ proveWithHash_wireDecodable hp,
    fun _ _ _ _ _ _ _ _ _ hp ↦ proveWithHash_climbInputsIn hp⟩

/-- **Completeness on the wire holds** (in the random-permutation model): trying `2^25` nonces
per proof of work, the honest prover's bytes for an execution within the verifier's size cap are
rejected by the verifier on bytes with probability at most `2^-256`. -/
theorem completenessOnBytes_holds : CompletenessOnBytes :=
  completenessOnBytes_of honestWireFacts completenessWithHash_holds

end LeanVM.Wire

/-- info: 'LeanVM.Wire.completenessOnBytes_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Wire.completenessOnBytes_holds
