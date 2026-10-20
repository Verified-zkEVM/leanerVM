/-
  LeanerVM.Protocol.EndToEnd.Execution

  From a stack satisfying the leanISA instance's relation to a valid execution: the adaptor's
  soundness composed with leanISA's constraint soundness.
-/

module

public import LeanerVM.Protocol.LeanIsa.Sound
public import LeanerVM.Arithmetization.Soundness.Theorem

/-!
# The extracted stack has an execution

Protocol blueprint Layer 13, `execution_of_extracted`: a stack `q` satisfying `M3Holds` of the
leanISA instance at admissible sizes, for well-formed bytecode, carries a witness
(`witnessOf`, the adaptor's read-back) that represents a valid execution of the program on the
input. It is the last two links of target T4's composition: `satisfiedBy_witnessOf` (the
adaptor's soundness) and `constraintSoundness` (leanISA Layers 9-10). Category A; nothing
transcribed. The witness is kept, as recursion (T6) needs it.
-/

namespace LeanerVM.Protocol.EndToEnd

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol.LeanIsa

@[expose] public section

/-- **The extracted stack has an execution.** On admissible sizes and well-formed bytecode, a
stack satisfying the leanISA instance's relation reads back to a witness that represents a valid
execution of the program on the input. -/
theorem execution_of_extracted (F : FlockSpec) {prog : Program} {input : PublicInput}
    {s : Sizes} {q : Column (leanIsaμ prog s)} (hsafe : SentinelSafe prog)
    (hs : s.Admissible prog) (h : M3Holds (leanIsaInstance F prog s) input q) :
    ∃ t, AssignmentRepresents (witnessOf F prog s q) t ∧ ValidExecution prog input t :=
  constraintSoundness hsafe (satisfiedBy_witnessOf F prog s q hs h)

end
end LeanerVM.Protocol.EndToEnd
