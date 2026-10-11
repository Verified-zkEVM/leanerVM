import LeanerVMTests.Arithmetization.Boundary
import LeanerVMTests.Arithmetization.Bytecode
import LeanerVMTests.Arithmetization.Channels
import LeanerVMTests.Arithmetization.Completeness.Balance
import LeanerVMTests.Arithmetization.Completeness.LongRun
import LeanerVMTests.Arithmetization.Completeness.Rows
import LeanerVMTests.Arithmetization.Completeness.Satisfied
import LeanerVMTests.Arithmetization.Completeness.Theorem
import LeanerVMTests.Arithmetization.Completeness.Witness
import LeanerVMTests.Arithmetization.Statement
import LeanerVMTests.Arithmetization.Tables
import LeanerVMTests.Imports
import LeanerVMTests.Parameters.Blake2s
import LeanerVMTests.Parameters.CleanField
import LeanerVMTests.Parameters.Field
import LeanerVMTests.Parameters.Generator
import LeanerVMTests.Parameters.Isa
import LeanerVMTests.Protocol.AmbientStacking
import LeanerVMTests.Protocol.Batch
import LeanerVMTests.Protocol.BitProductTable
import LeanerVMTests.Protocol.Bus
import LeanerVMTests.Protocol.BusSecurity
import LeanerVMTests.Protocol.ClaimWeights
import LeanerVMTests.Protocol.Field
import LeanerVMTests.Protocol.Fingerprint
import LeanerVMTests.Protocol.FixedColumns
import LeanerVMTests.Protocol.GrandProduct
import LeanerVMTests.Protocol.GrandProductPoly
import LeanerVMTests.Protocol.GrandProductSecurity
import LeanerVMTests.Protocol.Multilinear
import LeanerVMTests.Protocol.Opening
import LeanerVMTests.Protocol.Padding
import LeanerVMTests.Protocol.PowerBatching
import LeanerVMTests.Protocol.ProductTree
import LeanerVMTests.Protocol.PublicInput
import LeanerVMTests.Protocol.SideProduct
import LeanerVMTests.Protocol.Spine
import LeanerVMTests.Protocol.Stack
import LeanerVMTests.Protocol.Stacking
import LeanerVMTests.Protocol.Sumcheck
import LeanerVMTests.Protocol.TableSumcheck
import LeanerVMTests.Semantics.Blake2s
import LeanerVMTests.Semantics.Blake2sOutput
import LeanerVMTests.Semantics.ClosedWalk
import LeanerVMTests.Semantics.Executable
import LeanerVMTests.Semantics.Execution
import LeanerVMTests.Semantics.FillBlocks
import LeanerVMTests.Semantics.FillCycle
import LeanerVMTests.Semantics.FillPlan
import LeanerVMTests.Semantics.FillRows
import LeanerVMTests.Semantics.FillSteps
import LeanerVMTests.Semantics.FillerRows
import LeanerVMTests.Semantics.Instruction
import LeanerVMTests.Semantics.LongRun
import LeanerVMTests.Semantics.Memory
import LeanerVMTests.Semantics.PaddedImage
import LeanerVMTests.Semantics.PaddedImageRefutation
import LeanerVMTests.Semantics.PaddedRows
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
