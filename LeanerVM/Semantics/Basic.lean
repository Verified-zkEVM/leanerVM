module

public import LeanerVM.Parameters.Basic

/-!
# VM semantics

This layer holds the source-faithful instruction set (`Instruction`), the memory image and the
public input (`Memory`), the BLAKE2s compression relation (`Blake2s`), one step of the machine
(`Step`), and the execution loop with valid executions (`Execution`). `step` and `run` are
specifications, reasoned about through their lemmas: `gLog?` is noncomputable. `Executable` is a
pure executable carrier, with exact and fuel-bounded checkers proved equivalent to the
fixed-image execution relation; `TraceInput` checks the shape of an exported memory and its main
and filler row counts, and can validate the main run. The fill blocks and padded traces (`Fill*`,
`Padded*`) extend a valid execution with the filler steps the proof system pads with. These are
semantic results, not a correspondence to the Rust source. This layer must not depend on the
arithmetization or proof-system layers.
-/

namespace LeanerVM.Semantics

public section

end
end LeanerVM.Semantics
