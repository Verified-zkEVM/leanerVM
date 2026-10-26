/-
  LeanVM.Prover.WitnessColumns

  The executable columns of a valid execution are the instance's columns of the stack of its
  specification witness, every one of them, the `KECCAK` output lanes included.
-/

module

public import LeanVM.Prover.WitnessRows
public import LeanVM.Prover.WitnessSpec
public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance

/-!
# The columns of an execution

`traceWitness prog input t` is the specification's witness of an execution (`skelWitness` of its
run's skeletons, the witness `exists_childFor` builds), `traceSizes` the sizes it carries, and
`traceRows t` the executable pass over the run's steps. On a valid execution:

* the pass's tables are the witness's opcode tables, row for row (`tabs_trace`), its counters the
  memory and bytecode blocks' finalize counts;
* the sizes are the trace's memory log-size and the pass's row counts (`logMem_trace`,
  `rows_trace`), and the executable log-heights the instance's (`logs_trace`);
* **every column** (`cols_trace`): `colsOf` at the Python number of an instance column is that
  column of the stack of the witness, the `KECCAK` output lanes the instance's derived columns.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.Halting
open Air.Flat (EnsembleWitness)

@[expose] public section

variable {prog : Program} {input : PublicInput} {t : Trace prog}

/-! ## The specification's witness and the executable pass -/

/-- **The specification's witness of an execution**: the rows of its run's skeletons, its image,
the program (`skelWitness`; the witness of `exists_childFor`). -/
noncomputable def traceWitness (prog : Program) (input : PublicInput) (t : Trace prog) :
    EnsembleWitness (leanIsaEnsemble prog) :=
  skelWitness prog input t.image t.runSkels

/-- The executable pass over the steps of an execution's run. -/
noncomputable def traceRows (t : Trace prog) : Rows :=
  rowsOf (powIndex t.κ) t.image prog.logSize (traceSteps t).toArray

/-- A valid execution's memory is within `gLog?`'s address space. -/
theorem κ_lt_of_valid (hv : ValidExecution prog input t) : t.κ < 64 := by
  have := hv.1.2.1; unfold maxLogMem at this; omega

/-- The pass over a valid run keeps the invariant at the run's skeletons. -/
theorem rowsInv_trace (hv : ValidExecution prog input t) :
    RowsInv t.image prog.logSize (traceRows t) t.runSkels := by
  have := rowsInv_rowsOf (κ_lt_of_valid hv) t.image (traceSteps t) (stepOk_traceSteps hv.2)
  rwa [runSkels_eq_steps hv.2] at this

/-- The opcode tables of `skelWitness`. -/
theorem tableAt_skelWitness {κ : ℕ} (img : MemImage κ) (S : List Skel) (j : Fin 6) :
    tableAt (skelWitness prog input img S) ⟨j, by omega⟩ =
      Arithmetization.opTable img (imageData img) (skelRows img S) (tableOpcode j) := by
  fin_cases j <;> rfl

/-- The table of the opcode of table `j` is `j`. -/
theorem tableOf_tableOpcode (j : Fin 6) : tableOf (tableOpcode j) = j := by
  fin_cases j <;> rfl

/-- **The pass's tables are the witness's opcode tables.** -/
theorem tabs_trace (hv : ValidExecution prog input t) (j : Fin 6) :
    ((traceRows t).tabs.getD j #[]).toList =
      (tableAt (traceWitness prog input t) ⟨j, by omega⟩).table := by
  have h := (rowsInv_trace hv).tabs (tableOpcode j)
  rw [tableOf_tableOpcode] at h
  rw [h, traceWitness, tableAt_skelWitness]
  rfl

/-! ## The sizes -/

/-- The witness's memory log-size is the trace's. -/
theorem traceWitness_logSize (hv : ValidExecution prog input t) :
    (imageOf (traceWitness prog input t).data).1 = t.κ :=
  imageData_logSize t.image hv.1.2.1

/-- The witness has at least two memory cells. -/
theorem traceWitness_pos (hv : ValidExecution prog input t) :
    0 < (imageOf (traceWitness prog input t).data).1 := by
  rw [traceWitness_logSize hv]
  have := hv.1.1
  unfold minLogMem at this
  omega

/-- **The sizes of an execution**: those its specification witness carries (`witnessSizes`); a
placeholder when it carries none (never, on a valid execution). -/
noncomputable def traceSizes (prog : Program) (input : PublicInput) (t : Trace prog) : Sizes :=
  if h : 0 < (imageOf (traceWitness prog input t).data).1 then
    witnessSizes (traceWitness prog input t) h
  else ⟨1, Nat.one_pos, fun _ ↦ 0⟩

theorem traceSizes_eq (hv : ValidExecution prog input t) :
    traceSizes prog input t = witnessSizes (traceWitness prog input t) (traceWitness_pos hv) := by
  unfold traceSizes
  rw [dite_eq_left (traceWitness_pos hv)]

/-- The memory log-size is the trace's. -/
theorem logMem_trace (hv : ValidExecution prog input t) :
    (traceSizes prog input t).logMem = t.κ := by
  rw [traceSizes_eq hv]
  exact traceWitness_logSize hv

/-- The row counts are the pass's tables' sizes. -/
theorem rows_trace (hv : ValidExecution prog input t) (j : Fin 6) :
    (traceSizes prog input t).rows j = ((traceRows t).tabs.getD j #[]).size := by
  rw [traceSizes_eq hv, ← Array.length_toList, tabs_trace hv j]
  rfl

/-- The pass's row counts, as a list, are the sizes'. -/
theorem rowsList_trace (hv : ValidExecution prog input t) :
    (traceRows t).tabs.toList.map (·.size) = List.ofFn (traceSizes prog input t).rows := by
  have h6 := (rowsInv_trace hv).tabs_size
  apply List.ext_getElem (by simp [h6])
  intro i h1 h2
  have hi : i < 6 := by simpa [h6] using h1
  rw [List.getElem_map, List.getElem_ofFn, rows_trace hv ⟨i, hi⟩, Array.getElem_toList]
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (h6 ▸ hi)]

/-- **The executable log-heights are the instance's.** -/
theorem logs_trace (hv : ValidExecution prog input t) :
    tableLogsOf ((traceRows t).tabs.toList.map (·.size)) = List.ofFn (traceSizes prog input t).τ := by
  rw [rowsList_trace hv]
  exact logHeights_tableRows _

theorem logs_getD (hv : ValidExecution prog input t) (j : Fin 6) :
    (tableLogsOf ((traceRows t).tabs.toList.map (·.size))).getD j 0 =
      (traceSizes prog input t).τ j := by
  rw [logs_trace hv]
  fin_cases j <;> rfl

/-! ## Cells -/

/-- A table read through the pass is the witness's table. -/
theorem cellAt_eq {R : Array (Array K)} {T : Air.Flat.Table K} (h : R.toList = T.table) (x i : ℕ) :
    cellAt R x i = cellOf T x i := by
  unfold cellAt cellOf
  rw [← h, Array.getElem?_toList]

/-- The twelve-round states of the pass. -/
theorem midStates_getD (R : Array (Array K)) (h x : ℕ) (hx : x < 2 ^ h) :
    (midStates R h).getD x zeroState =
      keccakSegment 0 (laneState fun l : Fin 25 ↦ cellAt R x (13 + l.val)) := by
  simp only [midStates, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hx, dite_true,
    Option.getD_some]
  split_ifs with hr
  · rfl
  · have hz : (fun l : Fin 25 ↦ cellAt R x (13 + l.val)) = fun _ ↦ 0 := funext fun l ↦ by
      simp [cellAt, Array.getElem?_eq_none (Nat.not_lt.mp hr)]
    rw [hz, laneState_zero]
    rfl

/-- The twenty-four-round states of the pass. -/
theorem outStates_getD (R : Array (Array K)) (h x : ℕ) (hx : x < 2 ^ h) :
    (outStates R (midStates R h)).getD x zeroState =
      keccakSegment 1 (keccakSegment 0 (laneState fun l : Fin 25 ↦ cellAt R x (13 + l.val))) := by
  have hm := midStates_getD R h x hx
  have hsize : (midStates R h).size = 2 ^ h := by simp [midStates]
  have hx' : x < (midStates R h).size := by rw [hsize]; exact hx
  have hm' : (midStates R h)[x]'hx' =
      keccakSegment 0 (laneState fun l : Fin 25 ↦ cellAt R x (13 + l.val)) := by
    rw [← hm, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hx', Option.getD_some]
  simp only [outStates, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hx', dite_true,
    Option.getD_some, Fin.getElem_fin]
  split_ifs with hr
  · rw [hm']
    rfl
  · have hz : (fun l : Fin 25 ↦ cellAt R x (13 + l.val)) = fun _ ↦ 0 := funext fun l ↦ by
      simp [cellAt, Array.getElem?_eq_none (Nat.not_lt.mp hr)]
    rw [hz, laneState_zero]
    rfl

/-- The memory block's cells. -/
theorem memCell_trace (x : ℕ) (hx : x < 2 ^ t.κ) (k : ℕ) :
    cellOf (tableAt (traceWitness prog input t) 6) x k =
      (#[gpow x, g ^ skelMemFin t.image t.runSkels (gpow x), (t.image ⟨x, hx⟩).limb 0,
        (t.image ⟨x, hx⟩).limb 1, (t.image ⟨x, hx⟩).limb 2][k]?).getD 0 := by
  show ((List.ofFn fun i : Fin (2 ^ t.κ) ↦ rawRow (memRowOf t.image i
    (g ^ skelMemFin t.image t.runSkels (gpow i))))[x]?.bind (·[k]?)).getD 0 = _
  rw [List.getElem?_ofFn]
  simp [hx, rawRow, memRow_toArray, memRowOf]

/-- The bytecode block's finalize counts. -/
theorem bcCell_trace (x : ℕ) (hx : x < 2 ^ prog.logSize) :
    cellOf (tableAt (traceWitness prog input t) 7) x 1 = g ^ skelBcFin t.runSkels (gpow x) := by
  show ((List.ofFn fun i : Fin (2 ^ prog.logSize) ↦ rawRow (bytecodeRowOf prog i
    (g ^ skelBcFin t.runSkels (gpow i))))[x]?.bind (·[1]?)).getD 0 = _
  rw [List.getElem?_ofFn]
  simp [hx, rawRow, bytecodeRow_toArray, bytecodeRowOf]

end

end LeanVM.Prover
