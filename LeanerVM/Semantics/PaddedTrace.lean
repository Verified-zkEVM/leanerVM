/-
  LeanerVM.Semantics.PaddedTrace

  Padded traces, and the room and size conditions a trace must meet for its tables to be filled.
-/

module

public import LeanerVM.Semantics.FillPlan

/-!
# Padded traces

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`). Category A: written from the
blueprint's `constraintCompleteness`, which is false as stated, for two reasons found by audit and
each refuted by a test:

* **The image.** `AssignmentRepresents` forces the witness image to be the trace's, but
  `ValidExecution` pins the image only at the cells the run reads and at `g^0`, `g^1`, and
  `MemImage` is total. The padding rows of every table read and write cells of that same image, so
  the image must hold frames on which the fill blocks step. A valid trace whose image admits no
  `XOR` step exists for every program that starts with a `JUMP` to the sentinel
  (`tests/LeanerVMTests/Semantics/PaddedImageRefutation.lean`).
* **The size.** `Caps.heights` bounds every table by `2^32` rows while `Trace.steps` is unbounded:
  a witness needs at least `steps` rows over its eight tables, and a valid run of
  `1 + 33 * 2^30` steps exists. A trace that fits has at most `6 * 2^32` steps
  (`Trace.Fits.steps_le`), so that run is no fitting trace.

**The corrected target.** Completeness is stated for a *padded* trace and under a named condition
on the trace (roadmap decisions D1, D7 of the pull request):

* `t'.PaddedFrom t` says `t'` is `t` with its memory extended: the same steps, a larger memory
  log-size, and the same words below `2^t.κ`. The run of `t` is then the run of `t'` (the
  validity lemmas of `Semantics.PaddedRun`), so nothing about the machine changes; only the
  cells for the fill frames are added.
* `t.Fits` says the trace leaves room for them and keeps every table within the row cap:
  `room`, there is space above the image (`t.κ < maxLogMem`); `rows`, every table but `JUMP`
  filled to its target stays within `2^maxLogRows`; and `jump`, the `JUMP` table, which also takes
  one closing jump per traversal elsewhere, can be filled (`JumpFeasible`). Each is necessary for
  the construction and refuted when dropped.

Program-shape conditions stay fields of `WellFormedBytecode`; image and resource conditions concern
the trace, so they are `Trace.Fits`, a hypothesis of completeness only: soundness extracts its
trace from a witness, where `Caps` already holds. They are not part of `ValidExecution`, which is
the ISA-level notion; `docs/architecture.md` places resource hypotheses on the T2 and T4
completeness statements.

## Wrong readings excluded

* Padding does not change the run: `steps` is equal, and the words the run reads are below
  `2^t.κ`, where the images agree.
* The `JUMP` table is not independent of the others: `owed` adds one closing jump per traversal of
  every other table's fill (`Semantics.FillPlan`).
* `Fits.room` is not the verifier's cap on the memory log-size (that is in `ValidExecution`); it is
  the room the padded image needs above the committed one.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-- `t'` is `t` padded: the same number of steps, a memory log-size at least `t`'s, and `t`'s words
at the same indices. The cells above `2^t.κ` are the fill frames. -/
structure Trace.PaddedFrom {prog : Program} (t' t : Trace prog) : Prop where
  /-- The run is the same length: padding adds no main-run steps. -/
  steps_eq : t'.steps = t.steps
  /-- The memory only grows. -/
  κ_le : t.κ ≤ t'.κ
  /-- The words of `t` are the words of `t'` at the same indices. -/
  image_ext : ∀ i (hi : i < 2 ^ t.κ) (hi' : i < 2 ^ t'.κ), t'.image ⟨i, hi'⟩ = t.image ⟨i, hi⟩

/-- The rows of opcode `op` in the run of `t`: the states stepped from, whose fetched instruction
has that opcode. The final state is not stepped from, so it is dropped. -/
noncomputable def Trace.runRows {prog : Program} (t : Trace prog) (op : Opcode) : ℕ :=
  (t.regs.dropLast.filter fun r ↦ (prog.fetch r.pc).map Instr.opcode = some op).length

/-- The rows the `JUMP` table owes before its own fill: the run's `JUMP` rows, and one closing
jump for every traversal of the fill of every other table (`cpu/filler.rs:166-167`, `owed`). -/
noncomputable def Trace.owed {prog : Program} (t : Trace prog) : ℕ := jumpOwed t.runRows

/-- A trace leaves room for the fill blocks and keeps every table within the row cap. -/
structure Trace.Fits {prog : Program} (t : Trace prog) : Prop where
  /-- There is space above the image for the fill frames: `κ + 1 ≤ maxLogMem`. -/
  room : t.κ < maxLogMem
  /-- Every table but `JUMP`, filled to its target, has at most `2^maxLogRows` rows. -/
  rows : ∀ op, op ≠ .jump → fillTarget (t.runRows op) (minRows op) ≤ 2 ^ maxLogRows
  /-- The `JUMP` table can be filled: a power of two within the cap is at least the rows it owes
  and is not one more. -/
  jump : JumpFeasible t.owed

/-! ## Load-bearing lemmas -/

/-- A trace is padded from itself. -/
theorem Trace.PaddedFrom.refl {prog : Program} (t : Trace prog) : t.PaddedFrom t :=
  ⟨rfl, le_rfl, fun _ _ _ ↦ rfl⟩

/-- No table has more rows than the run has steps. -/
theorem Trace.runRows_le_steps {prog : Program} {t : Trace prog} {rf : Regs K}
    (h : run prog t.image t.steps Regs.initial = some rf) (op : Opcode) :
    t.runRows op ≤ t.steps := by
  unfold Trace.runRows
  refine (List.length_filter_le _ _).trans ?_
  rw [List.length_dropLast, Trace.regs_length h]
  simp

/-- A short valid trace with room above its image fits: with at most `2^20` steps every table, and
the `JUMP` table with the closing jumps of the fills, is within the row cap. A sufficient
condition, and the inhabitant of `Fits` for every small run. -/
theorem Trace.Fits.of_short {prog : Program} {t : Trace prog} {rf : Regs K}
    (h : run prog t.image t.steps Regs.initial = some rf) (hroom : t.κ < maxLogMem)
    (hs : t.steps ≤ 2 ^ 20) : t.Fits := by
  have hrows : ∀ op, t.runRows op ≤ 2 ^ 20 := fun op ↦ (t.runRows_le_steps h op).trans hs
  have h20 : 2 ^ 20 ≤ 2 ^ maxLogRows := Nat.pow_le_pow_right (by norm_num) (by decide)
  refine ⟨hroom, fun op _ ↦ fillTarget_le ((hrows op).trans h20) ?_, ?_⟩
  · refine le_trans ?_ h20
    cases op <;> simp only [minRows] <;> norm_num
  · refine jumpFeasible_of_le ?_
    have := jumpOwed_le (rows := t.runRows) (k := 20) (by norm_num) hrows
    unfold Trace.owed
    refine this.trans ?_
    norm_num


/-! ## The rows of a run -/

/-- Every state a valid run steps from fetches an instruction: the step that follows it succeeded. -/
theorem Trace.exists_fetch_of_mem_dropLast {prog : Program} {t : Trace prog} {rf : Regs K}
    (h : run prog t.image t.steps Regs.initial = some rf) {r : Regs K}
    (hr : r ∈ t.regs.dropLast) : ∃ ins, prog.fetch r.pc = some ins := by
  have hreg : t.regs = (List.range t.steps).filterMap
      (fun n ↦ run prog t.image n Regs.initial) ++ [rf] := by
    unfold Trace.regs
    rw [List.range_succ, List.filterMap_append]
    simp [h]
  rw [hreg, List.dropLast_concat] at hr
  obtain ⟨k, hk, hkr⟩ := List.mem_filterMap.mp hr
  have hk' := List.mem_range.mp hk
  obtain ⟨r₁, h₁, h₂⟩ := run_prefix (m := k) (n := t.steps - k)
    (by rwa [Nat.add_sub_cancel' hk'.le])
  rw [h₁] at hkr
  cases Option.some.inj hkr
  obtain ⟨n', hn'⟩ : ∃ n', t.steps - k = n' + 1 := ⟨t.steps - k - 1, by omega⟩
  rw [hn', run_succ] at h₂
  by_cases hpc : r.pc = prog.finalPc
  · simp [hpc] at h₂
  · rw [ite_eq_right hpc] at h₂
    obtain ⟨r₂, hs, -⟩ := Option.bind_eq_some_iff.mp h₂
    unfold step at hs
    obtain ⟨ins, hf, -⟩ := Option.bind_eq_some_iff.mp hs
    exact ⟨ins, hf⟩

/-- A list of states that all fetch an instruction has one row on exactly one of the six tables
each. -/
theorem sum_filter_opcode_length {prog : Program} (l : List (Regs K))
    (hl : ∀ r ∈ l, ∃ ins, prog.fetch r.pc = some ins) :
    (fillTables.map fun op ↦
      (l.filter fun r ↦ (prog.fetch r.pc).map Instr.opcode = some op).length).sum = l.length := by
  induction l with
  | nil => simp [fillTables]
  | cons r l ih =>
    obtain ⟨ins, hins⟩ := hl r List.mem_cons_self
    have ih' := ih fun r' hr' ↦ hl r' (List.mem_cons_of_mem _ hr')
    simp only [← List.countP_eq_length_filter] at ih' ⊢
    simp only [List.countP_cons, hins, Option.map_some, fillTables, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.length_cons] at ih' ⊢
    cases ins.opcode <;> simp at ih' <;> simp <;> omega

/-- The rows of the six tables add up to the steps of the run: every state stepped from has one
instruction, which has one opcode. -/
theorem Trace.sum_runRows {prog : Program} {t : Trace prog} {rf : Regs K}
    (h : run prog t.image t.steps Regs.initial = some rf) :
    (fillTables.map t.runRows).sum = t.steps := by
  have hlen : t.regs.dropLast.length = t.steps := by
    rw [List.length_dropLast, Trace.regs_length h]
    rfl
  rw [← hlen]
  exact sum_filter_opcode_length t.regs.dropLast fun r hr ↦
    Trace.exists_fetch_of_mem_dropLast h hr

/-- A run whose tables fit the row cap has at most six times the cap in steps: no table has more
than `2^maxLogRows` rows, the `JUMP` table because it owes at least its run rows and can be filled
within the cap. -/
theorem Trace.steps_le_of_sizes {prog : Program} {t : Trace prog} {rf : Regs K}
    (h : run prog t.image t.steps Regs.initial = some rf)
    (hrows : ∀ op, op ≠ .jump → fillTarget (t.runRows op) (minRows op) ≤ 2 ^ maxLogRows)
    (hjump : JumpFeasible t.owed) : t.steps ≤ 6 * 2 ^ maxLogRows := by
  have hop : ∀ op, t.runRows op ≤ 2 ^ maxLogRows := fun op ↦ by
    by_cases hj : op = .jump
    · subst hj
      obtain ⟨τ, hτ, h1, -⟩ := hjump
      have : t.runRows .jump ≤ t.owed := by
        unfold Trace.owed jumpOwed
        exact Nat.le_add_right _ _
      exact this.trans (h1.trans (Nat.pow_le_pow_right (by norm_num) hτ))
    · exact (le_fillTarget _ _).trans (hrows op hj)
  have hsum := List.sum_le_length_nsmul (fillTables.map t.runRows) (2 ^ maxLogRows)
    fun x hx ↦ by
      obtain ⟨op, -, rfl⟩ := List.mem_map.mp hx
      exact hop op
  rw [Trace.sum_runRows h, List.length_map, smul_eq_mul] at hsum
  have hlen : fillTables.length = 6 := rfl
  rw [hlen] at hsum
  exact hsum

/-- A valid trace that fits has at most six times the row cap in steps. -/
theorem Trace.Fits.steps_le {prog : Program} {t : Trace prog} {rf : Regs K}
    (hf : t.Fits) (h : run prog t.image t.steps Regs.initial = some rf) :
    t.steps ≤ 6 * 2 ^ maxLogRows :=
  Trace.steps_le_of_sizes h hf.rows hf.jump

end
end LeanerVM.Semantics
