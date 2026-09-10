module

public import LeanerVM.Parameters.Basic

/-!
# VM semantics

This layer holds the source-faithful instruction set (`Instruction`), the memory image and the
public input (`Memory`), the BLAKE2s compression relation (`Blake2s`), one step of the machine
(`Step`), and the execution loop with valid executions (`Execution`). `step` and `run` are
specifications, reasoned about through their lemmas: `gLog?` is noncomputable, and an
executable carrier for running executions is later work bridged to this specification. It must
not depend on the arithmetization or proof-system layers.
-/

namespace LeanerVM.Semantics

public section

end
end LeanerVM.Semantics
