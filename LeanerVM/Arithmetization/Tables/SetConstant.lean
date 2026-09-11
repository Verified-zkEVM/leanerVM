/-
  LeanerVM.Arithmetization.Tables.SetConstant

  The `SET_CONSTANT` table: one Clean component per row, sound and complete for `step`.
  A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Channels
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

**The component** `setTable` pulls the state `(pc, fp)` and pushes the fall-through successor
`(g·pc, fp)`, reads the bytecode entry `(SET, o, k₀, k₁, k₂, 0, 0, 0)` at `pc`, and reads the
cell `fp·o` carrying the immediate. It returns the pushed successor, and `Spec` is
`step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next` (see
`LeanerVM.Arithmetization.Tables.Xor` for the template).

## Wrong readings excluded

* The immediate's three lanes are bytecode coordinates `4, 5, 6` of the entry, the slots
  `DEREF` uses for `o₃, f_pc, f_fp` (roadmap acceptance test 16; Layer 4's `entry`).
* The word read at `fp·o` is the immediate itself, all three limbs: a row whose cell holds any
  other word fails `Spec` (the mutated row in the tests).
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
  -- The row is a step: from its registers the machine steps to the pushed successor.
  Spec r next data := step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next
  -- The honest row: the operand and immediate are the fetched instruction's, and the cell
  -- holds the immediate.
  ProverAssumptions r data _ :=
    (programOf data).fetch r.pc = some (.setConstant r.o (E.ofLimbs r.k[0] r.k[1] r.k[2])) ∧
    (imageOf data).2.read (r.fp * r.o) = some (E.ofLimbs r.k[0] r.k[1] r.k[2])
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, hk⟩ := h_holds
    obtain ⟨_, _, _, hvk, _, _⟩ := h_input
    subst hvk
    rw [set_entry, decode_entry, Option.some.injEq] at hdec
    subst hdec
    simp only [Vector.getElem_map] at hk
    rw [step_of_fetch_eq_some hfetch]
    simp [execute, guard, hk, Regs.next]
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨hfetch, hk⟩ := h_assumptions
    obtain ⟨_, _, _, hvk, _, _⟩ := h_input
    subst hvk
    simp only [Vector.getElem_map] at hfetch hk ⊢
    exact ⟨⟨_, hfetch, by rw [set_entry, decode_entry]⟩, hk⟩

end LeanerVM.Arithmetization
