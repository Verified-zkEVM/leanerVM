import LeanerVMTests.Arithmetization.Boundary
import LeanerVMTests.Arithmetization.Bytecode
import LeanerVMTests.Arithmetization.Channels
import LeanerVMTests.Arithmetization.Statement
import LeanerVMTests.Arithmetization.Tables
import LeanerVMTests.Imports
import LeanerVMTests.Parameters.Blake2s
import LeanerVMTests.Parameters.CleanField
import LeanerVMTests.Parameters.Field
import LeanerVMTests.Parameters.Generator
import LeanerVMTests.Semantics.Blake2s
import LeanerVMTests.Semantics.Executable
import LeanerVMTests.Semantics.Execution
import LeanerVMTests.Semantics.FillerRows
import LeanerVMTests.Parameters.Isa
import LeanerVMTests.Protocol.Field
import LeanerVMTests.Protocol.Spine
import LeanerVMTests.Semantics.Instruction
import LeanerVMTests.Semantics.Memory
import LeanerVMTests.Semantics.RustExport
import LeanerVMTests.Semantics.TraceInput

/-!
# leanerVM test aggregate

Every Lean test module other than the elaboration root is imported here. Repository validation
checks that this aggregate remains complete. It is a plain file because `LeanerVM.lean` is one
(see `CONTRIBUTING.md`).
-/
