module

public import LeanerVM.Semantics.Basic

/-!
# Arithmetization

This layer holds the bytecode encoding (`Bytecode`), the bus channels (`Channels`), and the six
opcode tables (`Tables/`), the latter plain files because they consume Clean, and will hold the
boundary blocks, the constraint statement, witness generation, and the refinement theorems
connecting satisfying assignments to `LeanerVM.Semantics` executions
(`docs/roadmap/leanisa-blueprint.md`, Layers 7 to 10).
-/

namespace LeanerVM.Arithmetization

public section

end
end LeanerVM.Arithmetization
