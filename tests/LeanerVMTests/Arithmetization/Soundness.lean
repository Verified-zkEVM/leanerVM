import LeanerVM.Arithmetization.Soundness
import LeanerVMTests.Arithmetization.Steps

/-!
# Tests: constraint soundness

On the hand-built witness of the constraint-statement tests
(`LeanerVMTests.Arithmetization.Statement`), with its program's sentinel safe
(`LeanerVMTests.Arithmetization.Steps.fill_sentinelSafe`).

**The computable trace.** `traceOf`, compiled, returns the trace of the run: four steps over the
image at `κ = 16`, the trace `fill_t1_instance` names (on the fixture with an empty memory
block, which `traceOf` does not read: `traceOf_fill_eq`). On the zero-count witness, whose rows
step the same way, it returns the same four steps: `traceOf` decides nothing about memory or
counts, and only `traceOf_valid` makes its trace a valid execution. On a witness without the
`JUMP` row to the sentinel the walk stops at `(g^3, 1)`, which no row pulls, and `traceOf`
returns nothing.

**The theorems applied.** `traceOf_valid`, `constraintSoundness`, `exists_run_of_balanced` and
`leanIsaTraceExtraction` on the honest witness; the run they give is the semantic tests' run.
-/

namespace LeanerVMTests.Arithmetization.Soundness

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Arithmetization.Statement LeanerVMTests.Arithmetization.Steps

/-! ## The computable trace -/

-- `traceOf` reads only the six opcode tables and the data, and the interpreter would build all
-- `2^16` rows of the fixture's memory block, with an address `g^i` each, before it reads
-- anything; so the compiled checks run on the fixture with an empty memory block, and
-- `traceOf_fill_eq` says that is the fixture's trace.

/-- An empty memory block over the fixture's data. -/
def memTEmpty : Air.Flat.Table K :=
  mkT memTable (size MemRow) [] fun _ h ↦ absurd h List.not_mem_nil

/-- The honest witness with an empty memory block. -/
def lightW : Air.Flat.EnsembleWitness (leanIsaEnsemble fillProg) :=
  mkW [xorT, mulT g, setT 1, derefT, jumpT, blakeT, memTEmpty, bcT]

/-- The zero-count witness with an empty memory block. -/
def lightZeroW : Air.Flat.EnsembleWitness (leanIsaEnsemble fillProg) :=
  mkW [xorT, mulT 1, setT 0, derefT, jumpT, blakeT, memTEmpty, bcT]

/-- The `JUMP` table without its row to the sentinel. -/
def jumpTNoExit : Air.Flat.Table K :=
  mkT jumpTable (size JumpRow + 2) (jumpT.table.drop 1) fun r hr ↦
    jumpT.uniform_width r (List.mem_of_mem_drop hr)

/-- The honest witness without the `JUMP` row to the sentinel, with an empty memory block. -/
def noExitW : Air.Flat.EnsembleWitness (leanIsaEnsemble fillProg) :=
  mkW [xorT, mulT g, setT 1, derefT, jumpTNoExit, blakeT, memTEmpty, bcT]

theorem fill_take : (fillW 1 g memCnt).tables.take 6 =
    [xorT, mulT g, setT 1, derefT, jumpT, blakeT] := rfl
theorem light_take : lightW.tables.take 6 = [xorT, mulT g, setT 1, derefT, jumpT, blakeT] := rfl

/-- The fixture's trace is the light witness's: they have the same opcode tables and data. -/
theorem traceOf_fill_eq : traceOf fillProg (fillW 1 g memCnt) = traceOf fillProg lightW := by
  unfold traceOf stateMap statePairs
  rw [fill_take, light_take, data_eq, show lightW.data = fillData from rfl]

-- The fixture's trace: four steps, at `κ = 16`.
#guard (traceOf fillProg lightW).map (·.steps) = some 4
#guard (traceOf fillProg lightW).map (·.κ) = some 16

-- The zero-count witness's rows step the same way: the same four steps.
#guard (traceOf fillProg lightZeroW).map (·.steps) = some 4

-- Without the `JUMP` row to the sentinel the walk stops at `(g^3, 1)`: no trace.
#guard (traceOf fillProg noExitW).isNone

/-! ## The theorems applied -/

/-- The honest witness represents a valid execution, which `traceOf` finds. -/
example : ∃ t, traceOf fillProg (fillW 1 g memCnt) = some t ∧
    AssignmentRepresents (fillW 1 g memCnt) t ∧ ValidExecution fillProg mulInput t :=
  traceOf_valid fill_sentinelSafe fill_satisfiedBy

example : ∃ t, AssignmentRepresents (fillW 1 g memCnt) t ∧ ValidExecution fillProg mulInput t :=
  constraintSoundness fill_sentinelSafe fill_satisfiedBy

/-- The run, read off the statement alone, is the semantic tests' run. -/
example : ∃ n, run fillProg fillImage n Regs.initial = some (Regs.final fillProg) := by
  have h := exists_run_of_balanced fill_sentinelSafe fill_satisfiedBy
  rw [data_eq, fill_imageOf] at h
  exact h

/-- The interface's trace is `traceOf`. -/
example : (leanIsaTraceExtraction fill_sentinelSafe).traceOf mulInput (fillW 1 g memCnt) =
    traceOf fillProg (fillW 1 g memCnt) := rfl

end LeanerVMTests.Arithmetization.Soundness
