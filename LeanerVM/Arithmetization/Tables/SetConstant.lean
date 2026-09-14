/-
  LeanerVM.Arithmetization.Tables.SetConstant

  The `SET_CONSTANT` table: one Clean component per row, sound and complete for the row's
  functional specification, its binding to the program together with Layer 3's `step`.
  A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Tables.Basic
import Clean.Circuit.Formal
import Clean.Utils.Tactics.CircuitProofStart

/-!
# The `SET_CONSTANT` table

leanISA roadmap Layer 6 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `93c9d1ef`. Category B: the columns
are `crates/lean_vm/src/tables.rs:532-543` (`mod set`, in that order) and the flushes
`tables.rs:553-566` (`SetTable::flushes`), matching specification §7.3
(`doc/leanvm/body/07-instruction-tables.tex:52-64`). There is no constraint.

**The row** `SetRow` is the column list: `pc, fp`; the operand `o`; the immediate `k` as three
limbs (`K_LO, K_HI, K_TOP`, the bytecode's spare slots); the memory count `r`; the bytecode
count `r_bc`.

**The contract.** `SetRowBindings r data` binds the row to the program alone: the instruction
at `pc` is `SET_CONSTANT o k` with the row's immediate `word k`, all three limbs; there is no
input word to bind, the immediate being part of the fetched instruction. `SetSpec r next data`
is the binding and the step; `set_spec_iff` expands it: the cell `fp·o` holds `word k` and the
successor is `(g·pc, fp)`; `set_spec_step` projects the step. `SetRowReads` is the two pull
guarantees, and `set_reads_iff` identifies it with `∃ next, SetSpec r next data` (see
`LeanerVM.Arithmetization.Tables.Xor` for the template).

**The component** `setTable` pulls the state `(pc, fp)` and pushes the fall-through successor
`(g·pc, fp)` (`set_output`), reads the bytecode entry `(SET, o, k₀, k₁, k₂, 0, 0, 0)` at `pc`,
and reads the cell `fp·o` carrying the immediate. It returns the pushed successor, and `Spec`
is `SetSpec`; `ProverAssumptions r data _ := ∃ next, SetSpec r next data`.

**Rows from steps.** `setRowOf data pc fp o k r rbc` is the row of a step that fetches
`SET_CONSTANT o k`: the immediate's limbs are the instruction's (`limbs k`); `setRowOf_spec`,
`set_row_exists`, `setRow_complete` and `set_reads_of_constraints` are the `XOR` statements.

## Wrong readings excluded

* The immediate's three lanes are bytecode coordinates `4, 5, 6` of the entry, the slots
  `DEREF` uses for `o₃, f_pc, f_fp` (roadmap acceptance test 16; Layer 4's `entry`).
* The word read at `fp·o` is the immediate itself, all three limbs: a row whose cell holds any
  other word fails `SetSpec` (the mutated row in the tests), and a row whose immediate limb is
  not the program's fails its binding.
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

/-! ## The row -/

/-- The `SET_CONSTANT` columns, in the order of `tables.rs:532-543`. -/
structure SetRow (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operand `o`. -/
  o : F
  /-- The immediate `k = k₀ + k₁·y + k₂·y²`, as limbs. -/
  k : Vector F 3
  /-- The read count of the cell `fp · o`. -/
  r : F
  /-- The read count of the bytecode entry at `pc`. -/
  rbc : F
  deriving ProvableStruct

/-! ## Load-bearing lemmas -/

/-- The bytecode tuple of a `SET_CONSTANT` row is the entry of the instruction it names
(Layer 4): the immediate's limbs are the entry's coordinates `2, 3, 4`. -/
theorem set_entry (o k0 k1 k2 : K) :
    #v[Opcode.setConstant.code] ++ #v[o, k0, k1, k2, 0, 0, 0] =
      entry (.setConstant o (E.ofLimbs k0 k1 k2)) := rfl

/-! ## The contract -/

/-- The row's binding to the program: the instruction at `pc` is `SET_CONSTANT o k` with the
row's immediate. -/
def SetRowBindings (r : SetRow K) (data : ProverData K) : Prop :=
  (programOf data).fetch r.pc = some (.setConstant r.o (E.ofLimbs r.k[0] r.k[1] r.k[2]))

/-- The functional specification of a `SET_CONSTANT` row: it is bound to the program, and from
its registers the machine steps to `next`. -/
def SetSpec (r : SetRow K) (next : Regs K) (data : ProverData K) : Prop :=
  SetRowBindings r data ∧ step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next

/-- The two pull guarantees of the row: the fetch, and the cell holding the immediate. -/
def SetRowReads (r : SetRow K) (data : ProverData K) : Prop :=
  (programOf data).fetch r.pc = some (.setConstant r.o (E.ofLimbs r.k[0] r.k[1] r.k[2])) ∧
  (imageOf data).2.read (r.fp * r.o) = some (E.ofLimbs r.k[0] r.k[1] r.k[2])

/-- `SetSpec`, expanded: the binding, the cell `fp·o` holds the immediate, and the successor is
the fall-through `(g·pc, fp)`. -/
theorem set_spec_iff (r : SetRow K) (next : Regs K) (data : ProverData K) :
    SetSpec r next data ↔
      SetRowBindings r data ∧
        (imageOf data).2.read (r.fp * r.o) = some (E.ofLimbs r.k[0] r.k[1] r.k[2]) ∧
        next = Regs.next ⟨r.pc, r.fp⟩ := by
  unfold SetSpec SetRowBindings
  constructor
  · rintro ⟨hfetch, hstep⟩
    refine ⟨hfetch, ?_⟩
    rw [step_of_fetch_eq_some hfetch] at hstep
    simp only [execute, Option.bind_eq_bind] at hstep
    cases hc : (imageOf data).2.read (r.fp * r.o) with
    | none => rw [hc] at hstep; exact absurd hstep (by simp)
    | some c =>
      rw [hc, Option.bind_some, guard_bind_eq_some_iff] at hstep
      obtain ⟨rfl, h⟩ := hstep
      simp only [Option.pure_def, Option.some.injEq] at h
      exact ⟨rfl, h.symm⟩
  · rintro ⟨hfetch, hk, rfl⟩
    refine ⟨hfetch, ?_⟩
    rw [step_of_fetch_eq_some hfetch]
    simp only [execute, hk, Option.bind_eq_bind, Option.bind_some, guard_bind_eq_some_iff,
      Option.pure_def, true_and]

/-- The step, projected out of the specification. -/
theorem set_spec_step {r : SetRow K} {next : Regs K} {data : ProverData K}
    (h : SetSpec r next data) : step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next :=
  h.2

/-- A row's pulls are reads of the data exactly when it is bound and steps. -/
theorem set_reads_iff (r : SetRow K) (data : ProverData K) :
    SetRowReads r data ↔ ∃ next, SetSpec r next data := by
  constructor
  · rintro ⟨hfetch, hk⟩
    exact ⟨_, (set_spec_iff _ _ _).mpr ⟨hfetch, hk, rfl⟩⟩
  · rintro ⟨next, h⟩
    obtain ⟨hfetch, hk, -⟩ := (set_spec_iff _ _ _).mp h
    exact ⟨hfetch, hk⟩

/-! ## The table -/

/-- The `SET_CONSTANT` table (specification §7.3; `tables.rs:532-586`): state step, bytecode
read of `(SET, o, k₀, k₁, k₂, 0, 0, 0)`, and the read of `fp·o` carrying the immediate. Returns
the pushed successor `(g·pc, fp)`. -/
def setTable : GeneralFormalCircuit K SetRow Regs where
  main r := do
    let next : Var Regs K := ⟨Expression.const g * r.pc, r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.setConstant.code)
      #v[r.o, r.k[0], r.k[1], r.k[2], 0, 0, 0]
    memRead (r.fp * r.o) r.r r.k
    pure next
  -- The push channels: their requirements are vacuous (Layer 5), the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Without core's `BitVec.reduceNeg` simproc, which misreads `-1 : K` (finding E6).
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The row is bound to the program, and steps to the pushed successor.
  Spec := SetSpec
  -- The semantic premise: the row is bound and steps somewhere.
  ProverAssumptions r data _ := ∃ next, SetSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, hk⟩ := h_holds
    obtain ⟨_, _, _, hvk, _, _⟩ := h_input
    subst hvk
    rw [set_entry, decode_entry, Option.some.injEq] at hdec
    subst hdec
    refine (set_spec_iff _ _ _).mpr ⟨?_, ?_, rfl⟩
    · simpa only [SetRowBindings, Vector.getElem_map] using hfetch
    · simpa only [Vector.getElem_map] using hk
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨hfetch, hk⟩ := (set_reads_iff _ _).mpr h_assumptions
    obtain ⟨_, _, _, hvk, _, _⟩ := h_input
    subst hvk
    simp only [Vector.getElem_map] at hfetch hk ⊢
    exact ⟨⟨_, hfetch, by rw [set_entry, decode_entry]⟩, hk⟩

/-- The returned successor: the fall-through `(g·pc, fp)`, for every environment. -/
theorem set_output (env : Environment K) (offset : ℕ) (r : Var SetRow K) :
    eval env ((setTable.main r).output offset) = ⟨g * (eval env r).pc, (eval env r).fp⟩ := by
  simp only [circuit_norm, setTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The constraints `main` emits on a row are its two pull guarantees. -/
theorem set_reads_of_constraints {env : Environment K} {r : Var SetRow K} {offset : ℕ}
    (h : ConstraintsHold.Soundness env ((setTable.main r).operations offset)) :
    SetRowReads (eval env r) env.data :=
  (set_reads_iff _ _).mpr ⟨_, (setTable.soundness offset env r (eval env r) rfl trivial h).1⟩

/-! ## Rows from steps -/

/-- The row of a step that fetches `SET_CONSTANT o k` from `(pc, fp)`: the registers, the
operand, the immediate's limbs, and the counts as parameters. -/
def setRowOf (pc fp o : K) (k : E) (rc rbc : K) : SetRow K :=
  ⟨pc, fp, o, #v[k.limb 0, k.limb 1, k.limb 2], rc, rbc⟩

/-- A valid step that fetches `SET_CONSTANT o k` is represented by `setRowOf`, with any
counts. -/
theorem setRowOf_spec {data : ProverData K} {pc fp o : K} {k : E} {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.setConstant o k))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (rc rbc : K) :
    SetSpec (setRowOf pc fp o k rc rbc) next data :=
  ⟨by show (programOf data).fetch pc = some (.setConstant o (E.ofLimbs (k.limb 0) (k.limb 1) (k.limb 2)))
      rw [ofLimbs_limb]; exact hfetch,
   hstep⟩

/-- A valid step that fetches `SET_CONSTANT o k` admits a row with the same registers and
operand and any counts. -/
theorem set_row_exists {data : ProverData K} {pc fp o : K} {k : E} {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.setConstant o k))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (rc rbc : K) :
    ∃ kv, SetSpec ⟨pc, fp, o, kv, rc, rbc⟩ next data :=
  ⟨_, setRowOf_spec hfetch hstep rc rbc⟩

/-- A row with the semantic premise satisfies the constraints of `main` in the row environment
over its data. -/
theorem setRow_complete {r : SetRow K} {data : ProverData K} (h : ∃ next, SetSpec r next data) :
    ConstraintsHold.Completeness (rowEnv data) ((setTable.main (const r)).operations 0) :=
  (setTable.completeness 0 (rowEnv data) (const r)
    (by simp only [circuit_norm, setTable, memRead, bytecodeRead, -BitVec.reduceNeg]) r
    ProvableType.eval_const_prover h).1

end LeanerVM.Arithmetization
