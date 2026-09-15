module

public import LeanerVM.Semantics.Basic

/-!
# Arithmetization

This layer holds the bytecode encoding (`Bytecode`), the bus channels (`Channels`), the six
opcode tables (`Tables/`), and the three boundary blocks (`Boundary`), the latter plain files
because they consume Clean, and will hold the constraint statement, witness generation, and the
refinement theorems connecting satisfying assignments to `LeanerVM.Semantics` executions
(`docs/roadmap/leanisa-blueprint.md`, Layers 8 to 10).
-/

namespace LeanerVM.Arithmetization

public section

end
end LeanerVM.Arithmetization
