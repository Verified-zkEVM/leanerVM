/-
  LeanerVM.Protocol.ProveExecution

  leanVM's honest prover from an execution: the witness generator, then the deployed prover.
-/

module

public import LeanerVM.Protocol.Prove
public import LeanerVM.Arithmetization.WitnessGen

/-!
# The honest prover from an execution

`proveExecution fuel prog input t ρ` proves the execution `t` of the program on the public input:
`witnessGen` computes leanISA's witness from the trace (the trace padded at the searched fill
starts), and `prove` proves the witness at the WHIR rate `ρ` with `fuel` candidate nonces per
grind. It is one computable term, `none` when either step returns none. Its completeness is
`proveExecution_complete` (`LeanerVM.Protocol.Headline`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Semantics LeanerVM.Arithmetization

@[expose] public section

/-- **leanVM's honest prover from an execution**: the witness generator, then the deployed
prover on its witness. -/
def proveExecution (fuel : ℕ) (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ) :
    Option (Proof PrunedMerklePaths) :=
  (witnessGen prog input t).bind fun w ↦ prove fuel prog input w ρ

end

end LeanerVM.Protocol
