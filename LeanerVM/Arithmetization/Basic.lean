module

public import LeanerVM.Semantics.Basic

/-!
# Arithmetization

This layer holds the bytecode encoding (`Bytecode`), the bus channels (`Channels`), the six
opcode tables (`Tables/`), and the three boundary blocks (`Boundary`), all Lean modules
over Clean. `Statement` defines `SatisfiedBy`, `AssignmentRepresents`, and the global bus,
image, program and boundary clauses. The opcode files contain local refinement and row-builder
proofs. The two global arithmetization/execution directions and the complete executable witness
generator remain obligations (`docs/roadmap/leanisa-blueprint.md`, Layers 9 and 10).
-/

namespace LeanerVM.Arithmetization

public section

end
end LeanerVM.Arithmetization
