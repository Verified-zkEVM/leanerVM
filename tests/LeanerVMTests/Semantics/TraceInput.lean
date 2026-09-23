import LeanerVM.Semantics.TraceInput
import LeanerVMTests.Semantics.Checker

/-!
# Finite export adaptation regressions

These test the Lean adapter's count and exact-image contract, independently of the maintained
Rust producer fixtures. Counts alone do not certify filler rows or actual opcode frequencies.
-/

namespace LeanerVMTests.Semantics.TraceInput

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Execution LeanerVMTests.Semantics.Checker

/-- A finite export of the consistent three-step image, with no filler announcements. -/
def exactInput : TraceInput where
  memory := Array.ofFn (staleImage (E.ofLimbs 1 0 0))
  mainCounts := #v[1, 0, 2, 0, 0, 0]
  rowCounts := #v[1, 0, 2, 0, 0, 0]
  cycles := 3

#guard validateInput staleProgram zeroInput exactInput
#guard (exactInput.adapt staleProgram).map (·.steps) = some 3
#guard !validateInput staleProgram zeroInput
  { exactInput with memory := Array.ofFn (staleImage 0) }
#guard !validateInput staleProgram zeroInput { exactInput with cycles := 20 }
#guard !validateInput staleProgram zeroInput
  { exactInput with mainCounts := #v[2, 0, 1, 0, 0, 0] }
#guard !validateInput staleProgram zeroInput
  { exactInput with memory := exactInput.memory.push 0 }
#guard !validateInput staleProgram zeroInput
  { exactInput with memory := #[] }
#guard !validateInput staleProgram zeroInput
  { exactInput with memory := Array.replicate 16 0 }

/-- A two-slot direct jump to an unexecuted SET sentinel. -/
def jumpProgram : Program := ⟨1, by decide, ![.jump 1 g 1, .setConstant 1 0]⟩

/-- One main transition, with nineteen additional rows announced. These numbers have the
same main/total distinction as the exact Rust fixture; filler validation is a separate check. -/
def fillerInput : TraceInput where
  memory := (Array.replicate (2 ^ minLogMem) (0 : E)).set! 0 (E.ofLimbs 1 0 0)
    |>.set! 1 (E.ofLimbs g 0 0)
  mainCounts := #v[0, 0, 0, 0, 1, 0]
  rowCounts := #v[1, 1, 1, 1, 8, 8]
  cycles := 20

/-- The public words read by the direct jump. -/
def jumpInput : PublicInput := ⟨![1, 0, g, 0]⟩

#guard fillerInput.mainSteps = 1
#guard fillerInput.fillerSteps = 19
#guard (fillerInput.adapt jumpProgram).map (·.steps) = some 1
#guard validateInput jumpProgram jumpInput fillerInput
#guard !validateInput jumpProgram jumpInput
  { fillerInput with mainCounts := fillerInput.rowCounts }

/-- An inhabited zero-step export of a one-slot program. -/
def emptyRun : TraceInput where
  memory := Array.replicate (2 ^ minLogMem) 0
  mainCounts := #v[0, 0, 0, 0, 0, 0]
  rowCounts := #v[0, 0, 0, 0, 0, 0]
  cycles := 0

#guard validateInput oneProg zeroInput emptyRun
#guard (emptyRun.adapt oneProg).map (·.steps) = some 0

end LeanerVMTests.Semantics.TraceInput
