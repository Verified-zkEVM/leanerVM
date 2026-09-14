/-
  LeanerVM.Arithmetization.Tables.SetConstant

  The `SET_CONSTANT` table: one Clean component per row, sound and complete for the relation
  the row refines, its binding to a program together with Layer 3's `step`.
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

**The relation.** `SetBindings prog mem r` binds the row to the program alone (`fetch_eq`): the
instruction at `pc` is `SET_CONSTANT o k` with the row's immediate `E.ofLimbs k[0] k[1] k[2]`,
all three limbs; there is no input word to bind, the immediate being part of the fetched
instruction, and the image is a parameter for the shape shared with the other tables.
`SetRefines prog mem r next` is the binding and the step (`step_eq`); `set_refines_iff` expands
it: the cell `fp·o` holds the immediate and the successor is `(g·pc, fp)` (see
`LeanerVM.Arithmetization.Tables.Xor` for the template). `SetSpec r next data` adapts the
relation to Clean's prover data and is the table's `Spec`; `ProverAssumptions r data _ :=
∃ next, SetSpec r next data` is the honest prover's row, proved of the row of any valid step
by `setRowOf_refines` (`set_step_complete`); completeness discharges the two pulls from it
through `set_refines_iff`, the immediate limbs `main` emits being the fetched instruction's
(Layer 4's `decode_entry`).

**The component** `setTable` pulls the state `(pc, fp)`, pushes and returns the fall-through
successor `(g·pc, fp)`, reads the bytecode entry `(SET, o, k₀, k₁, k₂, 0, 0, 0)` at `pc`, and
reads the cell `fp·o` carrying the immediate. `Spec` is `SetSpec`.

**Rows from steps.** `setRowOf pc fp o k r rbc` is the row of a step that fetches
`SET_CONSTANT o k`: the immediate's limbs are the instruction's, so the builder reads nothing
back and is computable; `setRowOf_refines` and `set_step_complete` are the `XOR` statements.

## Wrong readings excluded

* The immediate's three lanes are bytecode coordinates `4, 5, 6` of the entry, the slots
  `DEREF` uses for `o₃, f_pc, f_fp` (roadmap acceptance test 16; Layer 4's `entry`).
* The word read at `fp·o` is the immediate itself, all three limbs: a row whose cell holds any
  other word fails `SetRefines` (the mutated row in the tests), and a row whose immediate limb
  is not the program's fails its binding.
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

/-! ## The relation -/

/-- The row's binding to a program (the image is a parameter, for the shape shared with the
other tables): the instruction at `pc` is `SET_CONSTANT o k` with the row's immediate. -/
structure SetBindings {κ : ℕ} (prog : Program) (_mem : MemImage κ) (r : SetRow K) : Prop where
  /-- The instruction at `pc` is `SET_CONSTANT o k`, `k` the row's immediate. -/
  fetch_eq : prog.fetch r.pc = some (.setConstant r.o (E.ofLimbs r.k[0] r.k[1] r.k[2]))

/-- The relation a `SET_CONSTANT` row refines: it is bound to the program, and from its
registers the machine steps to `next`. -/
structure SetRefines {κ : ℕ} (prog : Program) (mem : MemImage κ) (r : SetRow K) (next : Regs K) :
    Prop where
  /-- The row is bound to the program. -/
  bindings : SetBindings prog mem r
  /-- From the row's registers the machine steps to `next`. -/
  step_eq : step prog mem ⟨r.pc, r.fp⟩ = some next

/-- `SetRefines`, expanded: the binding, the cell `fp·o` holds the immediate, and the successor
is the fall-through `(g·pc, fp)`. -/
theorem set_refines_iff {κ : ℕ} (prog : Program) (mem : MemImage κ) (r : SetRow K)
    (next : Regs K) :
    SetRefines prog mem r next ↔
      SetBindings prog mem r ∧
        mem.read (r.fp * r.o) = some (E.ofLimbs r.k[0] r.k[1] r.k[2]) ∧
        next = Regs.next ⟨r.pc, r.fp⟩ := by
  constructor
  · rintro ⟨⟨hfetch⟩, hstep⟩
    refine ⟨⟨hfetch⟩, ?_⟩
    rw [step_of_fetch_eq_some hfetch] at hstep
    simp only [execute, Option.bind_eq_bind] at hstep
    cases hc : mem.read (r.fp * r.o) with
    | none => rw [hc] at hstep; exact absurd hstep (by simp)
    | some c =>
      rw [hc, Option.bind_some, guard_bind_eq_some_iff] at hstep
      obtain ⟨rfl, h⟩ := hstep
      simp only [Option.pure_def, Option.some.injEq] at h
      exact ⟨rfl, h.symm⟩
  · rintro ⟨⟨hfetch⟩, hk, rfl⟩
    refine ⟨⟨hfetch⟩, ?_⟩
    rw [step_of_fetch_eq_some hfetch]
    simp only [execute, hk, Option.bind_eq_bind, Option.bind_some, guard_bind_eq_some_iff,
      Option.pure_def, true_and]

/-! ## The adapter to the prover data -/

/-- The table's `Spec`: the row refines `SetRefines` over the program and the image the prover
data names. -/
def SetSpec (r : SetRow K) (next : Regs K) (data : ProverData K) : Prop :=
  SetRefines (programOf data) (imageOf data).2 r next

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
  -- The row refines the relation over the data's program and image, to the pushed successor.
  Spec := SetSpec
  -- The honest prover's row: written from a valid step, it is bound and steps somewhere.
  -- Proved of the row built from any valid step by `setRowOf_refines`; see
  -- `set_step_complete`.
  ProverAssumptions r data _ := ∃ next, SetSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, hk⟩ := h_holds
    obtain ⟨_, _, _, hvk, _, _⟩ := h_input
    subst hvk
    -- The pulled tuple is the entry of `SET_CONSTANT` with the row's operand and immediate
    -- (Layer 4).
    obtain rfl :=
      Option.some.inj ((decode_entry (.setConstant input_o (E.ofLimbs _ _ _))).symm.trans hdec)
    refine (set_refines_iff _ _ _ _).mpr ⟨⟨?_⟩, ?_, rfl⟩
    · simpa only [Vector.getElem_map] using hfetch
    · simpa only [Vector.getElem_map] using hk
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The two pull guarantees, from the semantic premise: the tuple `main` emits is the
    -- fetched instruction's entry (Layer 4).
    obtain ⟨next, h⟩ := h_assumptions
    obtain ⟨⟨hfetch⟩, hk, -⟩ := (set_refines_iff _ _ _ _).mp h
    obtain ⟨_, _, _, hvk, _, _⟩ := h_input
    subst hvk
    simp only [Vector.getElem_map] at hfetch hk ⊢
    exact ⟨⟨_, hfetch, decode_entry (.setConstant _ (E.ofLimbs _ _ _))⟩, hk⟩

/-! ## Rows from steps -/

/-- The row of a step that fetches `SET_CONSTANT o k` from `(pc, fp)`: the registers, the
operand, the immediate's limbs, and the counts as parameters. -/
def setRowOf (pc fp o : K) (k : E) (rc rbc : K) : SetRow K :=
  ⟨pc, fp, o, #v[k.limb 0, k.limb 1, k.limb 2], rc, rbc⟩

/-- A valid step that fetches `SET_CONSTANT o k` is represented by `setRowOf`, with any
counts: the honest prover's row refines the relation, which is `ProverAssumptions` over the
data. -/
theorem setRowOf_refines {κ : ℕ} {prog : Program} {mem : MemImage κ} {pc fp o : K} {k : E}
    {next : Regs K} (hfetch : prog.fetch pc = some (.setConstant o k))
    (hstep : step prog mem ⟨pc, fp⟩ = some next) (rc rbc : K) :
    SetRefines prog mem (setRowOf pc fp o k rc rbc) next :=
  ⟨⟨by show prog.fetch pc = some (.setConstant o (E.ofLimbs (k.limb 0) (k.limb 1) (k.limb 2)))
       rw [ofLimbs_limb]; exact hfetch⟩,
   hstep⟩

/-- Every valid `SET_CONSTANT` step has a satisfying row, from the step alone: the constraints
of `main` hold of `setRowOf` in the row environment over the data. -/
theorem set_step_complete {data : ProverData K} {pc fp o : K} {k : E} {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.setConstant o k))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (rc rbc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((setTable.main (const (setRowOf pc fp o k rc rbc))).operations 0) :=
  (setTable.completeness 0 (rowEnv data) (const _)
    -- No witness slot: the row environment uses the local witnesses vacuously.
    (by simp only [circuit_norm, setTable, memRead, bytecodeRead, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover ⟨_, setRowOf_refines hfetch hstep rc rbc⟩).1

end LeanerVM.Arithmetization
