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
import LeanerVMTests.Parameters.Isa
import LeanerVMTests.Protocol.AmbientStacking
import LeanerVMTests.Protocol.BitProductTable
import LeanerVMTests.Protocol.ClaimWeights
import LeanerVMTests.Protocol.Field
import LeanerVMTests.Protocol.Fingerprint
import LeanerVMTests.Protocol.FixedColumns
import LeanerVMTests.Protocol.GrandProduct
import LeanerVMTests.Protocol.GrandProductSecurity
import LeanerVMTests.Protocol.Multilinear
import LeanerVMTests.Protocol.Padding
import LeanerVMTests.Protocol.ProductTree
import LeanerVMTests.Protocol.PublicInput
import LeanerVMTests.Protocol.Spine
import LeanerVMTests.Protocol.Stack
import LeanerVMTests.Protocol.Stacking
import LeanerVMTests.Semantics.Blake2s
import LeanerVMTests.Semantics.Blake2sOutput
import LeanerVMTests.Semantics.Executable
import LeanerVMTests.Semantics.Execution
import LeanerVMTests.Semantics.FillBlocks
import LeanerVMTests.Semantics.FillPlan
import LeanerVMTests.Semantics.FillerRows
import LeanerVMTests.Semantics.Instruction
import LeanerVMTests.Semantics.Memory
import LeanerVMTests.Semantics.PaddedRun
import LeanerVMTests.Semantics.PaddedTrace
import LeanerVMTests.Semantics.RustExport
import LeanerVMTests.Semantics.TraceInput

/-!
# leanerVM test aggregate

Every Lean test module other than the elaboration root is imported here. Repository validation
checks that this aggregate remains complete. It is a plain file because `LeanerVM.lean` is one
(see `CONTRIBUTING.md`).
-/
