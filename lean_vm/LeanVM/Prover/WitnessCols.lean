/-
  LeanVM.Prover.WitnessCols

  Every executable column of a valid execution is the instance's column of the stack of its
  specification witness, at the verifier's global column number.
-/

module

public import LeanVM.Prover.WitnessColumns

/-!
# Every column

`cols_trace`: on a valid execution, `colsOf` at `pyCol c` is the instance's column `c` read off
`stackOf` of the specification witness, for every column `c`: the memory's (its limbs and its
finalize counts), `BFCNT`, `QKECCAK` (`qkeccak_trace`), the opcode tables' columns, the `KECCAK`
input lanes and spare columns among them, and the `KECCAK` output lanes, which the instance
derives (`column_toArray_out`).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.Verifier
open Air.Flat (EnsembleWitness)

@[expose] public section

/-! ## The executable dispatch -/

/-- Each opcode table's width. -/
def tableWidth : ℕ → ℕ
  | 0 => 15
  | 1 => 15
  | 2 => 8
  | 3 => 15
  | 4 => 14
  | 5 => 90
  | _ => 90

/-- The instance's opcode tables have these widths. -/
theorem width_opIdx_eq : ∀ j : Fin 6, width (opIdx j) = tableWidth j := by decide +kernel

/-- The Python's table bases are `tableBase`. -/
theorem globalColumnBases_getD : ∀ j : Fin 6, globalColumnBases.getD j 0 = tableBase j := by
  decide +kernel

/-- The columns, by number. -/
theorem colsOf_getD {κ : ℕ} (img : MemoryImage κ) (acc : Rows) (logs : List ℕ) (n : ℕ)
    (hn : n < 163) :
    (colsOf img acc logs).getD n #[] =
      columnAt img acc logs (midStates (acc.tabs.getD 5 #[]) (logs.getD 5 0))
        (outStates (acc.tabs.getD 5 #[]) (midStates (acc.tabs.getD 5 #[]) (logs.getD 5 0))) n := by
  simp only [colsOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hn, dite_true,
    Option.getD_some]

/-- The column of an opcode table's column number: an output lane derived, the table's column
otherwise. -/
theorem columnAt_base {κ : ℕ} (img : MemoryImage κ) (acc : Rows) (logs : List ℕ)
    (mids outs : Array KeccakState) (j : ℕ) (hj : j < 6) (i : ℕ) (hi : i < tableWidth j) :
    columnAt img acc logs mids outs (tableBase j + i) =
      if j = 5 ∧ 38 ≤ i ∧ i < 63 then
        Array.ofFn (n := 2 ^ logs.getD 5 0) fun x ↦ laneK (outs.getD x.val zeroState) (i - 38)
      else tableColumn (acc.tabs.getD j #[]) (logs.getD j 0) i := by
  have hb : 6 ≤ tableBase j := by interval_cases j <;> decide
  have hidx : tableIndexOf (tableBase j + i) = j := by
    interval_cases j <;> simp only [tableBase, tableWidth] at hi ⊢ <;> unfold tableIndexOf <;>
      split_ifs <;> omega
  unfold columnAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [hidx, Nat.add_sub_cancel_left]

/-- The memory's limb columns, by number. -/
theorem columnAt_limb {κ : ℕ} (img : MemoryImage κ) (acc : Rows) (logs : List ℕ)
    (mids outs : Array KeccakState) (k : ℕ) (hk : k < 3) :
    columnAt img acc logs mids outs k = Array.ofFn (n := 2 ^ κ) fun x ↦ (img x).limb ⟨k, hk⟩ := by
  interval_cases k <;> rfl

theorem columnAt_three {κ : ℕ} (img : MemoryImage κ) (acc : Rows) (logs : List ℕ)
    (mids outs : Array KeccakState) : columnAt img acc logs mids outs 3 = acc.mem := rfl

theorem columnAt_four {κ : ℕ} (img : MemoryImage κ) (acc : Rows) (logs : List ℕ)
    (mids outs : Array KeccakState) : columnAt img acc logs mids outs 4 = acc.bc := rfl

theorem columnAt_five {κ : ℕ} (img : MemoryImage κ) (acc : Rows) (logs : List ℕ)
    (mids outs : Array KeccakState) :
    columnAt img acc logs mids outs 5 = qkeccakColumn (acc.tabs.getD 5 #[]) (logs.getD 5 0) mids :=
  rfl

/-! ## The output lanes -/

section Out

variable {prog : Program} (w : EnsembleWitness (leanIsaEnsemble prog))
  (hp : 0 < (imageOf w.data).1)

/-- **An output lane of the stack**, as an array: the last twelve rounds of the first twelve of
each row's input lanes. -/
theorem column_toArray_out (c : Col) (h : IsOut c) :
    ((leanIsaInstance prog (witnessSizes w hp)).column (stackOf prog (witnessSizes w hp) w)
        c).values.toArray =
      Array.ofFn (n := 2 ^ (witnessSizes w hp).τ 5) fun x ↦
        stateLanes (keccakSegment 1 (keccakSegment 0
          (laneState fun l : Fin 25 ↦ cellOf (tableAt w 5) x (13 + l.val))))
          ⟨c.2.val - 38, by have := h.2.2; omega⟩ := by
  obtain ⟨j, i⟩ := c
  obtain ⟨hj, h38, h63⟩ := h
  change j = opIdx 5 at hj
  subst hj
  refine (congrArg (fun c : Col ↦ ((leanIsaInstance prog (witnessSizes w hp)).column
    (stackOf prog (witnessSizes w hp) w) c).values.toArray) (eq_outCol (i := i) h38 h63)).trans ?_
  refine Array.ext (by simp only [Vector.size_toArray, Array.size_ofFn]; rfl) fun x h1 h2 ↦ ?_
  have hx : x < 2 ^ (witnessSizes w hp).τ 5 := by simpa using h2
  rw [Vector.getElem_toArray, Array.getElem_ofFn]
  exact column_getElem_out w hp _ x hx

end Out

/-! ## Every column of an execution -/

variable {prog : Program} {input : PublicInput} {t : Execution prog}

/-- The pass's tables, by number. -/
theorem tabs_trace' (hv : ValidExecution prog input t) (j : ℕ) (hj : j < 6) :
    ((traceRows t).tabs.getD j #[]).toList =
      (tableAt (traceWitness prog input t) ⟨j, by omega⟩).table :=
  tabs_trace hv ⟨j, hj⟩

/-- **The memory columns**, computed: the image's limbs and the finalize counts. -/
theorem memColumn_trace (hv : ValidExecution prog input t) (logs : List ℕ)
    (mids outs : Array KeccakState) (k : Fin 4) :
    columnAt t.memory (traceRows t) logs mids outs k =
      (witnessColumn prog (witnessSizes (traceWitness prog input t) (traceWitness_pos hv))
        (traceWitness prog input t) (memCol k)).toArray := by
  have hlog := traceWitness_logSize (input := input) hv
  have hI := rowsInv_trace (input := input) hv
  apply Array.ext_getElem?
  intro x
  have hR : (witnessColumn prog (witnessSizes (traceWitness prog input t) (traceWitness_pos hv))
      (traceWitness prog input t) (memCol k)).toArray[x]? =
      if x < 2 ^ t.logMemorySize then some (cellOf (tableAt (traceWitness prog input t) 6) x (memRowCell k))
      else none := by
    rw [Vector.getElem?_toArray]
    show (Vector.ofFn fun y : Fin (2 ^ (imageOf (traceWitness prog input t).data).1) ↦
      cellOf (tableAt (traceWitness prog input t) 6) y (memRowCell k))[x]? = _
    rw [Vector.getElem?_ofFn]
    by_cases hx : x < 2 ^ t.logMemorySize
    · rw [dite_eq_left_of_eq_true (eq_true (by rw [hlog]; exact hx)), ite_eq_left hx]
    · rw [dite_eq_right_of_eq_false (eq_false (by rw [hlog]; exact hx)), ite_eq_right hx]
  rw [hR]
  obtain ⟨k, hk⟩ := k
  by_cases hx : x < 2 ^ t.logMemorySize
  · rw [ite_eq_left hx, memCell_trace x hx]
    by_cases hk3 : k < 3
    · rw [columnAt_limb _ _ _ _ _ k hk3, Array.getElem?_ofFn, dite_eq_left_of_eq_true (eq_true hx)]
      interval_cases k <;> simp [memRowCell]
    · obtain rfl : k = 3 := by omega
      rw [columnAt_three, Array.getElem?_eq_getElem (by rw [hI.mem.1]; exact hx), hI.mem.2]
      simp [memRowCell, skelMemFin]
  · rw [ite_eq_right hx]
    by_cases hk3 : k < 3
    · rw [columnAt_limb _ _ _ _ _ k hk3, Array.getElem?_ofFn, dite_eq_right_of_eq_false (eq_false hx)]
    · obtain rfl : k = 3 := by omega
      rw [columnAt_three, Array.getElem?_eq_none (by rw [hI.mem.1]; omega)]

/-- **The bytecode's finalize counts**, computed. -/
theorem bfcntColumn_trace (hv : ValidExecution prog input t) (logs : List ℕ)
    (mids outs : Array KeccakState) :
    columnAt t.memory (traceRows t) logs mids outs 4 =
      (witnessColumn prog (witnessSizes (traceWitness prog input t) (traceWitness_pos hv))
        (traceWitness prog input t) bfcntCol).toArray := by
  have hI := rowsInv_trace (input := input) hv
  rw [columnAt_four]
  apply Array.ext_getElem?
  intro x
  rw [Vector.getElem?_toArray]
  show _ = (Vector.ofFn fun y : Fin (2 ^ prog.logSize) ↦
    cellOf (tableAt (traceWitness prog input t) 7) y 1)[x]?
  rw [Vector.getElem?_ofFn]
  by_cases hx : x < 2 ^ prog.logSize
  · rw [dite_eq_left_of_eq_true (eq_true hx), bcCell_trace (input := input) x hx,
      Array.getElem?_eq_getElem (by rw [hI.bc.1]; exact hx), hI.bc.2]
    rfl
  · rw [dite_eq_right_of_eq_false (eq_false hx), Array.getElem?_eq_none (by rw [hI.bc.1]; omega)]

/-- **`QKECCAK`**, computed once per step: the witness's. -/
theorem qkeccak_trace (hv : ValidExecution prog input t) {logs : List ℕ}
    (hl : logs.getD 5 0 =
      (witnessSizes (traceWitness prog input t) (traceWitness_pos hv)).τ 5) :
    qkeccakColumn ((traceRows t).tabs.getD 5 #[]) (logs.getD 5 0)
        (midStates ((traceRows t).tabs.getD 5 #[]) (logs.getD 5 0)) =
      (keccakWitness prog (witnessSizes (traceWitness prog input t) (traceWitness_pos hv))
        (traceWitness prog input t)).toArray := by
  have hR : ((traceRows t).tabs.getD 5 #[]).toList =
      (tableAt (traceWitness prog input t) 5).table := tabs_trace' hv 5 (by omega)
  rw [hl]
  unfold qkeccakColumn keccakWitness
  rw [Vector.toArray_ofFn]
  dsimp only
  congr 1
  funext i
  have hx : i.val % 2 ^ (witnessSizes (traceWitness prog input t) (traceWitness_pos hv)).τ 5 <
      2 ^ (witnessSizes (traceWitness prog input t) (traceWitness_pos hv)).τ 5 :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  split_ifs with h1 h2
  · rw [inLaneOf_eq _ (traceWitness_pos hv)]
    exact cellAt_eq hR _ _
  · rw [midStates_getD _ _ _ hx]
    have hin : (fun l : Fin 25 ↦ cellAt ((traceRows t).tabs.getD 5 #[])
        (i.val % 2 ^ (witnessSizes (traceWitness prog input t) (traceWitness_pos hv)).τ 5)
        (13 + l.val)) = inLaneOf prog (witnessSizes (traceWitness prog input t) (traceWitness_pos hv))
          (traceWitness prog input t)
          (i.val % 2 ^ (witnessSizes (traceWitness prog input t) (traceWitness_pos hv)).τ 5) :=
      funext fun l ↦ by rw [inLaneOf_eq _ (traceWitness_pos hv)]; exact cellAt_eq hR _ _
    exact congrArg (fun L ↦ laneK (keccakSegment 0 (laneState L))
      (i.val / 2 ^ (witnessSizes (traceWitness prog input t) (traceWitness_pos hv)).τ 5 - 25)) hin
  · exact cellAt_eq hR _ _

/-- **Every column of an execution.** On a valid execution, the executable columns at the
Python number of an instance column are that column of the stack of the specification witness
at its sizes: the committed columns, the `KECCAK` input lanes and spare columns, and the derived
`KECCAK` output lanes. -/
theorem cols_trace (hv : ValidExecution prog input t) (c : Col) :
    (colsOf t.memory (traceRows t) (tableLogsOf ((traceRows t).tabs.toList.map (·.size)))).getD
        (pyCol c) #[] =
      ((inst prog (traceSizes prog input t)).column
        (stackOf prog (traceSizes prog input t) (traceWitness prog input t)) c).values.toArray := by
  rw [colsOf_getD _ _ _ _ (pyCol_lt c)]
  have hl : ∀ j (hj : j < 6), (tableLogsOf ((traceRows t).tabs.toList.map (·.size))).getD j 0 =
      (witnessSizes (traceWitness prog input t) (traceWitness_pos hv)).τ ⟨j, hj⟩ := by
    intro j hj
    rw [← traceSizes_eq hv]
    exact logs_getD hv ⟨j, hj⟩
  generalize tableLogsOf ((traceRows t).tabs.toList.map (·.size)) = logs at hl
  rw [traceSizes_eq hv]
  have hI := rowsInv_trace hv
  rcases c with ⟨⟨j, hj⟩, i⟩
  match j, hj, i with
  | 0, _, i =>
    have hnv : ¬ IsVirtual (memCol i) := fun hk ↦ by
      have := congrArg Fin.val hk.1; simp [memCol, opIdx] at this
    exact (congrArg (columnAt t.memory (traceRows t) logs _ _) (pyCol_memCol i)).trans
      ((memColumn_trace hv _ _ _ i).trans (column_toArray_committed _ _ _ hnv).symm)
  | 1, _, i =>
    obtain ⟨i, hi1⟩ := i
    obtain rfl : i = 0 := by change i < 1 at hi1; omega
    exact (congrArg (columnAt t.memory (traceRows t) logs _ _) pyCol_bfcntCol).trans
      ((bfcntColumn_trace hv _ _ _).trans
        (column_toArray_committed _ _ bfcntCol (by decide)).symm)
  | 2, _, i =>
    obtain ⟨i, hi1⟩ := i
    obtain rfl : i = 0 := by change i < 1 at hi1; omega
    exact (congrArg (columnAt t.memory (traceRows t) logs _ _) pyCol_keccakCol).trans
      ((columnAt_five _ _ _ _ _).trans ((qkeccak_trace hv (hl 5 (by omega))).trans
        (column_toArray_committed _ _ keccakCol not_isVirtual_keccakCol).symm))
  | j + 3, hj, i =>
    have hj6 : j < 6 := by omega
    obtain ⟨i, hi⟩ := i
    have hiw : i < tableWidth j :=
      calc i < width (opIdx ⟨j, hj6⟩) := hi
        _ = tableWidth j := width_opIdx_eq ⟨j, hj6⟩
    have hpy : pyCol ⟨⟨j + 3, hj⟩, ⟨i, hi⟩⟩ = tableBase j + i :=
      (pyCol_opIdx ⟨j, hj6⟩ ⟨i, hi⟩).trans (congrArg (· + i) (globalColumnBases_getD ⟨j, hj6⟩))
    refine (congrArg (columnAt t.memory (traceRows t) logs _ _) hpy).trans
      ((columnAt_base _ _ _ _ _ j hj6 i hiw).trans ?_)
    by_cases hout : j = 5 ∧ 38 ≤ i ∧ i < 63
    · rw [ite_eq_left hout]
      obtain ⟨rfl, h38, h63⟩ := hout
      have hO : IsOut ⟨opIdx 5, ⟨i, hi⟩⟩ := ⟨rfl, h38, h63⟩
      have hl5 : logs.getD 5 0 =
          (witnessSizes (traceWitness prog input t) (traceWitness_pos hv)).τ 5 := hl 5 (by omega)
      refine Eq.trans ?_ (column_toArray_out _ _ _ hO).symm
      rw [hl5]
      congr 1
      funext x
      rw [outStates_getD _ _ _ x.isLt]
      have hin : (fun l : Fin 25 ↦ cellAt ((traceRows t).tabs.getD 5 #[]) x.val (13 + l.val)) =
          fun l : Fin 25 ↦ cellOf (tableAt (traceWitness prog input t) 5) x (13 + l.val) :=
        funext fun l ↦ cellAt_eq (tabs_trace' hv 5 (by omega)) _ _
      exact congrArg (fun L ↦ laneK (keccakSegment 1 (keccakSegment 0 (laneState L)))
        (i - 38)) hin
    · rw [ite_eq_right hout]
      have hO : ¬ IsOut ⟨opIdx ⟨j, hj6⟩, ⟨i, hi⟩⟩ := fun h ↦ hout ⟨by
        have := congrArg Fin.val h.1; simp [opIdx] at this; omega, h.2⟩
      refine Eq.trans ?_ (column_toArray_table _ _ ⟨j, hj6⟩ ⟨i, hi⟩ hO).symm
      rw [← hl j hj6]
      unfold tableColumn
      congr 1
      funext x
      exact cellAt_eq (tabs_trace' hv j hj6) _ _

end

end LeanVM.Prover
