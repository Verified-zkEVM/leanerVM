import LeanerVM.Arithmetization.Soundness
import LeanerVMTests.Arithmetization.Steps

/-!
# Tests: constraint soundness

On the hand-built witness of the constraint-statement tests
(`LeanerVMTests.Arithmetization.Statement`), with its program's sentinel safe
(`LeanerVMTests.Arithmetization.Steps.fill_sentinelSafe`).

**The computable trace.** `traceOf`, compiled, returns the trace of the run: four steps, on a
light witness with the fixture's six opcode tables and a one-row memory block at `κ = 0`, whose
walk is the fixture's (`traceOf_fill_eq`: the walk reads only the six opcode tables' rows, never
the prover data). On the zero-count witness, whose rows step the same way, it returns the same
four steps: `traceOf` decides nothing about memory or counts, and only `traceOf_valid` makes its
trace a valid execution. On a witness without the `JUMP` row to the sentinel the walk stops at
`(g^3, 1)`, which no row pulls, and `traceOf` returns nothing.

**The theorems applied.** `traceOf_valid`, `constraintSoundness`, `exists_run_of_balanced` and
`leanIsaTraceExtraction` on the honest witness; the run they give is the semantic tests' run.
-/

namespace LeanerVMTests.Arithmetization.Soundness

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Arithmetization.Statement LeanerVMTests.Arithmetization.Steps
open Air.Flat (Component EnsembleWitness)

/-! ## The computable trace -/

-- `traceOf` reads only the six opcode tables' rows, and the interpreter would build all `2^16`
-- rows of the fixture's memory block, with an address `g^i` each, to derive the prover data; so
-- the compiled checks run on light witnesses with a one-row memory block at `κ = 0`, and
-- `traceOf_fill_eq` says that the walk is the fixture's.

/-- A one-row memory block at `κ = 0`: cell `g^0`, the zero word. -/
def memT0 : Air.Flat.Table K :=
  mkT (memComponent 0) ([(⟨1, 1, #v[0, 0, 0]⟩ : MemRow K)].map rawRow)
    (rawRows_size [(⟨1, 1, #v[0, 0, 0]⟩ : MemRow K)]) (by decide)
    ⟨rfl, fun i hi ↦ by
      obtain rfl : i = 0 := by simpa using hi
      refine (memMode_fixedAt_iff (κ := 0) hi (by decide) _).mpr ?_
      show (fromElements (Air.Flat.rowPrefix (size MemRow)
        (rawRow (⟨1, 1, #v[0, 0, 0]⟩ : MemRow K))) : MemRow K).idx = gpow 0
      rw [fromElements_rawRow]
      exact (pow_zero g).symm⟩

/-- A light witness at `κ = 0` with the opcode tables `ts`. -/
def lightOf (ts : List (Air.Flat.Table K))
    (hc : (ts ++ [memT0, bcT]).map (·.component) = (leanIsaEnsemble fillProg 0).tables := by rfl) :
    EnsembleWitness (leanIsaEnsemble fillProg 0) :=
  witnessOfTables fillProg 0 (PublicIO.ofInput mulInput) (ts ++ [memT0, bcT]) hc

/-- The honest witness's opcode tables, light. -/
def lightW : EnsembleWitness (leanIsaEnsemble fillProg 0) :=
  lightOf [xorT, mulT g, setT 1, derefT, jumpT, blakeT]

/-- The zero-count witness's opcode tables, light. -/
def lightZeroW : EnsembleWitness (leanIsaEnsemble fillProg 0) :=
  lightOf [xorT, mulT 1, setT 0, derefT, jumpT, blakeT]

/-- The `JUMP` table without its row to the sentinel. -/
def jumpTNoExit : Air.Flat.Table K :=
  mkT jumpComponent (jumpT.table.drop 1)
    (fun r hr ↦ jumpT.uniform_width r (List.mem_of_mem_drop hr))
    (by rw [List.length_drop]; exact le_trans (Nat.sub_le _ _) jumpT.length_le)

/-- The honest witness without the `JUMP` row to the sentinel, light. -/
def noExitW : EnsembleWitness (leanIsaEnsemble fillProg 0) :=
  lightOf [xorT, mulT g, setT 1, derefT, jumpTNoExit, blakeT]

/-! ## Proof helpers -/

/-- An interaction evaluated on a row reads the row only, not the data. -/
theorem eval_interaction_congr (row : Array K) (D D' : ProverData K) (i : AbstractInteraction K) :
    i.eval (Environment.fromArray row D) = i.eval (Environment.fromArray row D') := by
  simp only [AbstractInteraction.eval, eval_fromArray row D D']

/-- A row's messages depend on its table's component, not on the table's data. -/
theorem rowMessagesOn_congr {t t' : Air.Flat.Table K} (hc : t.component = t'.component)
    (row : Array K) (c : RawChannel K) (d : BusDir) :
    rowMessagesOn t row c d = rowMessagesOn t' row c d := by
  have he : AbstractInteraction.eval (Environment.fromArray row t.data) =
      AbstractInteraction.eval (Environment.fromArray row t'.data) :=
    funext (eval_interaction_congr row t.data t'.data)
  simp only [rowMessagesOn, Operations.interactionValues, Air.Flat.Table.environment, hc, he]

/-- The state pairs depend on the six opcode tables' components and rows only. -/
theorem statePairs_congr {κ κ' : ℕ} {w : EnsembleWitness (leanIsaEnsemble fillProg κ)}
    {w' : EnsembleWitness (leanIsaEnsemble fillProg κ')}
    (h : (w.tables.take 6).map (fun t ↦ (t.component, t.table)) =
      (w'.tables.take 6).map (fun t ↦ (t.component, t.table))) :
    statePairs w = statePairs w' := by
  unfold statePairs
  generalize w.tables.take 6 = l at h ⊢
  generalize w'.tables.take 6 = l' at h ⊢
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons t l ih =>
    cases l' with
    | nil => simp at h
    | cons t' l' =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨hc, ht⟩, h⟩ := h
      simp only [List.flatMap_cons, ih l' h, ht, rowMessagesOn_congr hc]

/-- The fixture's and the light witness's opcode tables have the same components and rows. -/
theorem fill_light_take :
    ((fillW 1 g memCnt).tables.take 6).map (fun t ↦ (t.component, t.table)) =
      (lightW.tables.take 6).map (fun t ↦ (t.component, t.table)) := by
  have h1 : (fillW 1 g memCnt).tables.map (fun t ↦ (t.component, t.table)) =
      [xorT, mulT g, setT 1, derefT, jumpT, blakeT, memT memCnt, bcT].map
        (fun t ↦ (t.component, t.table)) := witnessOfTables_map (hc := rfl)
  have h2 : lightW.tables.map (fun t ↦ (t.component, t.table)) =
      [xorT, mulT g, setT 1, derefT, jumpT, blakeT, memT0, bcT].map
        (fun t ↦ (t.component, t.table)) := witnessOfTables_map (hc := rfl)
  rw [List.map_take, List.map_take, h1, h2]
  simp only [List.map_cons, List.take_succ_cons, List.take_zero]

/-- The fixture's walk is the light witness's. -/
theorem traceOf_fill_eq :
    (traceOf fillProg (fillW 1 g memCnt)).map (·.steps) =
      (traceOf fillProg lightW).map (·.steps) := by
  unfold traceOf stateMap
  rw [statePairs_congr fill_light_take]
  simp only [Option.map_map, Function.comp_def]

-- The fixture's walk: four steps.
#guard (traceOf fillProg lightW).map (·.steps) = some 4

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
  rw [fill_imageOf] at h
  exact h

/-- The interface's trace is `traceOf`. -/
example : (leanIsaTraceExtraction fill_sentinelSafe).traceOf mulInput minLogMem
    (fillW 1 g memCnt) = traceOf fillProg (fillW 1 g memCnt) := rfl

end LeanerVMTests.Arithmetization.Soundness
