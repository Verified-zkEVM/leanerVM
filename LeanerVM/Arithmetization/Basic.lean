module

public import LeanerVM.Semantics.Basic

/-!
# Arithmetization

This layer holds the bytecode encoding (`Bytecode`), the bus channels (`Channels`), the six
opcode tables (`Tables/`) and the three boundary blocks (`Boundary`), all Lean modules over
Clean, and the constraint statement (`Statement`: `SatisfiedBy`, `AssignmentRepresents`).
`constraintSoundness` (`Soundness`, from the lookup argument in `Bus` and the per-row facts in
`Rows`, `Messages` and `Steps`) takes a satisfying assignment to a valid `LeanerVM.Semantics`
execution; `constraintCompleteness` (`Completeness/`) takes a valid execution to a satisfying
assignment; `Equivalence` composes the two. The witness `Completeness/` builds is
`noncomputable`: it proves that one exists and does not compute it.
-/

namespace LeanerVM.Arithmetization

public section

end
end LeanerVM.Arithmetization
