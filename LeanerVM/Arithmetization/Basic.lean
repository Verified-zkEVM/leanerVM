module

public import LeanerVM.Semantics.Basic

/-!
# Arithmetization

This layer holds the bytecode encoding (`Bytecode`) and the bus channels (`Channels`, a plain
file because it consumes Clean), and will hold the six opcode tables, the boundary blocks, the
constraint statement, witness generation, and the refinement theorems connecting satisfying
assignments to `LeanerVM.Semantics` executions (`docs/roadmap/leanisa-blueprint.md`, Layers 6
to 10).
-/

namespace LeanerVM.Arithmetization

public section

end
end LeanerVM.Arithmetization
