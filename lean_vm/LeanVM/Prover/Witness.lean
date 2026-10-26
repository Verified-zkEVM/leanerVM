/-
  LeanVM.Prover.Witness

  The executable witness of an execution is the specification's: `checkTrace` decides a valid
  execution within the cap, and `witness?` returns, from the same run, the announced sizes, every
  column of the instance and the stack of the specification witness, which is a child's witness
  (`ChildFor`).
-/

module

public import LeanVM.Prover.WitnessCols
public import LeanVM.Prover.WitnessStack
public import LeanVM.Guest.Child.Honest

/-!
# The witness of an execution

The specification prover runs at `traceWitness prog input t` (`skelWitness` of the run's
skeletons) and `traceSizes prog input t` (the sizes it carries, `witnessSizes`), with the stack
`stackOf prog s w`. The executable prover runs `witness?` (`Statement/Prover/Columns.lean`).

* `checkTrace_iff` (`WitnessRun.lean`): `checkTrace` is a valid execution whose committed size is
  at most `2^28`; `isSome_witness?`: `witness?` returns exactly when it holds.
* `witness?_spec`: then `witness?` returns data meeting `WitnessSpec`: the memory log-size and
  row counts of `traceSizes`, `μ = leanIsaμ`, every column at its Python number the instance's
  column of `stackOf` (the `KECCAK` output lanes included), the stack `stackOf`'s cells, and the
  announcement `announce`.
* `childFor_trace`: the specification witness at its sizes is a child's witness at every valid
  rate (`exists_childFor`, for the concrete witness).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.Halting LeanVM.Protocol.Verifier
open LeanVM.Guest.Child
open Air.Flat (EnsembleWitness)

@[expose] public section

variable {prog : Program} {input : PublicInput} {t : Trace prog}

/-! ## The specification witness is a child's -/

/-- The run's skeletons are sound. -/
theorem skelOk_runSkels (hv : ValidExecution prog input t) :
    ∀ sk ∈ t.runSkels, SkelOk prog t.image sk := by
  intro sk hsk
  rw [runSkels_eq hv.2] at hsk
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hsk
  exact skAt_ok hv.2 (List.mem_range.mp hk)

/-- The specification witness's opcode tables hold the run's rows. -/
theorem length_traceWitness (j : Fin 6) :
    (tableAt (traceWitness prog input t) ⟨j, by omega⟩).table.length =
      Skel.count (tableOpcode j) t.runSkels := by
  rw [traceWitness, tableAt_skelWitness]
  show (List.map _ (List.filter _ _)).length = _
  rw [List.length_map, skelRows, length_filter_mkRows]

/-- The specification witness carries its sizes. -/
theorem ofWitness_traceWitness (hv : ValidExecution prog input t) :
    Sizes.ofWitness (traceWitness prog input t) = some (traceSizes prog input t) := by
  rw [traceSizes_eq hv]
  unfold Sizes.ofWitness
  simp only [traceWitness_pos hv, dite_true]
  rfl

/-- **The specification witness is a child's witness**, for a valid execution within the cap and
a valid rate: `exists_childFor`, for the concrete witness. -/
theorem childFor_trace (hv : ValidExecution prog input t)
    (hbudget : t.committedSize ≤ 2 ^ 28) {ρ : ℕ} (hρ : validRate ρ) :
    ChildFor prog input t ρ (traceWitness prog input t) (traceSizes prog input t) := by
  have hcount : ∀ op, t.count op = t.runRows op := Trace.count_eq_runRows hv.2
  have hheight : ∀ op, 2 ^ Nat.clog 2 (t.count op) ≤ t.committedSize := by
    intro op
    have : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
    have hk : 2 ^ Nat.clog 2 (t.count .keccak) ≤ 2 ^ max (Nat.clog 2 (t.count .keccak)) 9 :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    simp only [Trace.committedSize]
    cases op <;> omega
  have hcap : (2 : ℕ) ^ 28 ≤ 2 ^ maxLogRows := Nat.pow_le_pow_right (by norm_num) (by decide)
  have hrows : ∀ op, t.runRows op ≤ 2 ^ maxLogRows := fun op ↦ by
    rw [← hcount]
    exact (Nat.le_pow_clog (by norm_num) _).trans (((hheight op).trans hbudget).trans hcap)
  obtain ⟨⟨hmin, hκ, hw0, hw1⟩, hrun⟩ := hv
  have hS := skelOk_runSkels (input := input) ⟨⟨hmin, hκ, hw0, hw1⟩, hrun⟩
  have hw : SatisfiedBy prog input (traceWitness prog input t) :=
    skelWitness_satisfiedBy prog input t.image _ hmin hκ hS (runSkels_state_perm hrun)
      (fun op ↦ (t.count_runSkels op).trans_le (hrows op)) hw0 hw1
  have hrep : AssignmentRepresents (traceWitness prog input t) t := by
    refine skelWitness_represents prog input hκ hrun _ (fun sk hsk ↦ (hS sk hsk).2) ?_
    intro k hk
    rw [runSkels_eq hrun]
    exact List.mem_map_of_mem (List.mem_range.mpr hk)
  have hv : ValidExecution prog input t := ⟨⟨hmin, hκ, hw0, hw1⟩, hrun⟩
  have hs0 := ofWitness_traceWitness hv
  rw [traceSizes_eq hv] at hs0 ⊢
  have hmem : (witnessSizes (traceWitness prog input t) (traceWitness_pos hv)).logMem = t.κ :=
    hrep.κ_eq
  have hr : ∀ j : Fin 6,
      (witnessSizes (traceWitness prog input t) (traceWitness_pos hv)).rows j =
        t.count (tableOpcode j) :=
    fun j ↦ (length_traceWitness j).trans ((t.count_runSkels _).trans (hcount _).symm)
  have htotal : (LeanIsa.blocks prog
      (witnessSizes (traceWitness prog input t) (traceWitness_pos hv))).total =
      t.committedSize := by
    have e : tableOpcode 0 = .xor ∧ tableOpcode 1 = .mulNative ∧ tableOpcode 2 = .setConstant ∧
        tableOpcode 3 = .deref ∧ tableOpcode 4 = .jump ∧ tableOpcode 5 = .keccak := by decide
    rw [blocks_total_eq, hmem, pow_add 2 _ 6]
    simp only [Sizes.τ, hr, e, Trace.committedSize]
    have f0 : tableLogFloors.getD ((0 : Fin 6) : ℕ) 0 = 0 := rfl
    have f1 : tableLogFloors.getD ((1 : Fin 6) : ℕ) 0 = 0 := rfl
    have f2 : tableLogFloors.getD ((2 : Fin 6) : ℕ) 0 = 0 := rfl
    have f3 : tableLogFloors.getD ((3 : Fin 6) : ℕ) 0 = 0 := rfl
    have f4 : tableLogFloors.getD ((4 : Fin 6) : ℕ) 0 = 0 := rfl
    have f5 : tableLogFloors.getD ((5 : Fin 6) : ℕ) 0 = 9 := rfl
    simp only [f0, f1, f2, f3, f4, f5, Nat.max_zero]
    ring
  refine ⟨⟨hρ, hw, hs0, ⟨?_, ?_, fun j ↦ (hr j).trans_le (by rw [hcount]; exact hrows _),
    leanIsaμ_le_of_total_le (htotal ▸ hbudget)⟩, hrep⟩, htotal⟩
  · rw [hmem]
    exact hmin
  · rw [hmem]
    exact hκ

/-! ## The executable data -/

/-- **What the executable data of an execution is**: the sizes of the specification witness
(`traceSizes`), its stack's number of variables, every column of the instance read off its stack
by Python column number, the stack's cells, and the announcement. -/
structure WitnessSpec (prog : Program) (input : PublicInput) (t : Trace prog) (W : Witness) :
    Prop where
  /-- The memory log-size. -/
  logMem : W.logMem = (traceSizes prog input t).logMem
  /-- The six row counts. -/
  rows : W.rows = List.ofFn (traceSizes prog input t).rows
  /-- The stack's number of variables. -/
  μ : W.μ = leanIsaμ prog (traceSizes prog input t)
  /-- Every column, the `KECCAK` output lanes included. -/
  cols : ∀ c : Col, W.cols.getD (pyCol c) #[] =
    ((inst prog (traceSizes prog input t)).column
      (stackOf prog (traceSizes prog input t) (traceWitness prog input t)) c).values.toArray
  /-- The stack. -/
  stack : W.stack =
    (stackOf prog (traceSizes prog input t) (traceWitness prog input t)).values.toArray
  /-- The announced sizes and rate. -/
  announce : ∀ ρ, W.announce ρ = LeanVM.Protocol.EndToEnd.Front.announce (traceSizes prog input t) ρ

/-- The executable column log-sizes are the instance's. -/
theorem kappas_trace (hv : ValidExecution prog input t) :
    columnKappas t.κ prog.logSize (tableLogsOf ((traceRows t).tabs.toList.map (·.size))) =
      pyKappas prog (traceSizes prog input t) := by
  rw [logs_trace hv, ← logMem_trace hv]
  rfl

/-- **The data built from a valid run is the specification's.** -/
theorem buildWitness_spec (hv : ValidExecution prog input t) :
    WitnessSpec prog input t (buildWitness prog t (powIndex t.κ) (traceSteps t).toArray) := by
  have hk := kappas_trace hv
  have hμ : (placementsOf (columnKappas t.κ prog.logSize
      (tableLogsOf ((traceRows t).tabs.toList.map (·.size))))).2 =
      leanIsaμ prog (traceSizes prog input t) := by
    rw [hk]; exact placementsOf_snd prog _
  refine ⟨logMem_trace hv |>.symm, rowsList_trace hv, hμ, cols_trace hv, ?_, fun ρ ↦ ?_⟩
  · show stackArray (placementsOf (columnKappas t.κ prog.logSize
        (tableLogsOf ((traceRows t).tabs.toList.map (·.size))))).2
      (colsOf t.image (traceRows t) (tableLogsOf ((traceRows t).tabs.toList.map (·.size))))
      (stackOrderOf (columnKappas t.κ prog.logSize
        (tableLogsOf ((traceRows t).tabs.toList.map (·.size))))) = _
    rw [hμ, hk, stackOrderOf_pyKappas]
    refine stackArray_eq _ _ _ fun c hc ↦ ?_
    have hmem : c ∈ committedColumns := List.mem_mergeSort.mp hc
    have hnv : ¬ IsVirtual c := by
      simp only [committedColumns, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
        at hmem
      exact hmem.2
    rw [cols_trace hv, traceSizes_eq hv]
    exact column_toArray_committed _ _ c hnv
  · show ((t.κ :: (traceRows t).tabs.toList.map (·.size)) ++ [ρ]).map eOfNat = _
    rw [rowsList_trace hv, ← logMem_trace hv]
    rfl

/-- **The executable witness of a valid execution within the cap** is built from its run. -/
theorem witness?_eq (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 28) :
    witness? prog input t = some (buildWitness prog t (powIndex t.κ) (traceSteps t).toArray) := by
  unfold witness?
  rw [ite_eq_left ((boundaryOK_iff input t).mpr hv.1)]
  simp only
  rw [runSteps_eq t (κ_lt_of_valid hv), ite_eq_left hv.2]
  simp only
  rw [committedSizeOf_eq t (opCount_traceSteps hv.2), ite_eq_left (show _ ≤ maxCommitted from hcap)]

/-- **The executable witness** of a valid execution within the cap meets `WitnessSpec`. -/
theorem witness?_spec (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 28) :
    ∃ W, witness? prog input t = some W ∧ WitnessSpec prog input t W :=
  ⟨_, witness?_eq hv hcap, buildWitness_spec hv⟩

/-- `witness?` returns exactly when `checkTrace` holds. -/
theorem isSome_witness? (prog : Program) (input : PublicInput) (t : Trace prog) :
    (witness? prog input t).isSome = checkTrace prog input t := by
  unfold witness? checkTrace
  by_cases hb : boundaryOK input t = true
  · simp only [hb, Bool.true_and, ↓reduceIte]
    cases runSteps (powIndex t.κ) (powIndex prog.logSize) prog t with
    | none => rfl
    | some steps =>
      by_cases h : committedSizeOf prog.logSize t.κ (opCount steps) ≤ maxCommitted <;> simp [h]
  · simp [hb]

/-- `witness?` returns exactly on a valid execution within the cap. -/
theorem isSome_witness?_iff (prog : Program) (input : PublicInput) (t : Trace prog) :
    (witness? prog input t).isSome = true ↔
      ValidExecution prog input t ∧ t.committedSize ≤ 2 ^ 28 := by
  rw [isSome_witness?, checkTrace_iff]

end

end LeanVM.Prover
