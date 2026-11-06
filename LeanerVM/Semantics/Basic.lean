module

public import LeanerVM.Parameters.Basic

/-!
# VM semantics

This layer holds the source-faithful instruction set (`Instruction`), the memory image and the
public input (`Memory`), the BLAKE2s compression relation (`Blake2s`), one step of the machine
(`Step`), and the execution loop with valid executions (`Execution`). `step` and `run` are
specifications, reasoned about through their lemmas: `gLog?` is noncomputable, and a
pure executable carrier is `Executable`, with exact and fuel-bounded checkers proved
equivalent to the fixed-image execution relation. `RunTrace` gives ordered states and
`TraceInput` checks exported main/filler rows. These are semantic results; Rust-source
correspondence remains separate. This layer must not depend on arithmetization or protocol.
-/

namespace LeanerVM.Semantics

public section

end
end LeanerVM.Semantics
