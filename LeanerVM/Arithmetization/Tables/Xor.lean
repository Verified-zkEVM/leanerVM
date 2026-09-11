/-
  LeanerVM.Arithmetization.Tables.Xor

  The `XOR` table: one Clean component per row, sound and complete for `step`.
  A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Channels
import Clean.Circuit.Formal
import Clean.Utils.Tactics.CircuitProofStart

/-!
# The `XOR` table

leanISA roadmap Layer 6 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `93c9d1ef`. Category B: the columns
are `crates/lean_vm/src/tables.rs:436-455` (`mod arith`, in that order), the flushes
`tables.rs:487-500` (`Arith::flushes` with `is_xor`), the result coordinates `tables.rs:470-476`
(`arith_result`, the lane-wise sum), all matching specification §7.1
(`doc/leanvm/body/07-instruction-tables.tex:9-26`). There is no constraint: the bus balance is
the assertion `[o_C] = [o_A] + [o_B]` (§5, "M3").

**The row** `XorRow` is the column list: `pc, fp`; the operands `o_A, o_B, o_C`; the two read
words `v_A, v_B` as three limbs each; the memory counts `r_A, r_B, r_C`; the bytecode count
`r_bc`. The result word is never a column: its limbs ride the third memory read as the sums
`v_{A,i} + v_{B,i}`.

**The component** `xorTable` pulls the state `(pc, fp)` and pushes the fall-through successor
`(g·pc, fp)`, reads the bytecode entry `(XOR, o_A, o_B, o_C, 0, 0, 0, 0)` at `pc`, and reads the
three cells `fp·o_A`, `fp·o_B`, `fp·o_C` with the third carrying the sum. It returns the pushed
successor, so that `Spec` says of the row's registers and the pushed state exactly that the
machine steps from the one to the other: `step (programOf data) (imageOf data).2 ⟨pc, fp⟩ =
some next`, Layer 3's `step` on the program and image named by the prover data (Layer 5).

**Soundness** assumes the guarantees of the four pulls (memory reads are the image's words,
the bytecode entry is the fetched instruction) and concludes `Spec`; the requirements of the
three pushes are vacuous, since the push channels guarantee nothing (Layer 5: what a push must
satisfy is this `Spec`). **Completeness** takes `ProverAssumptions`: the honest row, whose
operands are the fetched instruction's and whose three reads, the sum included, are the
image's words at the operand cells.

## Wrong readings excluded

* The result is `v_A + v_B` limb by limb, in `E` (`add_limbs`): a row whose result read
  carries any other word fails `Spec`, since `step` compares the word read at `fp·o_C` with
  the sum (acceptance test: the mutated row in the tests).
* The successor is `(g·pc, fp)`, never `(pc + 1, fp)` (acceptance test 3).
* Every bytecode coordinate is explicit, the four spare slots as literal zeros
  (status finding R24; Layer 4's `decode` rejects a nonzero spare slot).
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

/-! ## The row -/

/-- The `XOR` columns, in the order of `tables.rs:436-455`. -/
structure XorRow (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operand `o_A`. -/
  oA : F
  /-- The operand `o_B`. -/
  oB : F
  /-- The operand `o_C`. -/
  oC : F
  /-- The word read at `fp · o_A`, as limbs. -/
  vA : Vector F 3
  /-- The word read at `fp · o_B`, as limbs. -/
  vB : Vector F 3
  /-- The read count of the cell `fp · o_A`. -/
  rA : F
  /-- The read count of the cell `fp · o_B`. -/
  rB : F
  /-- The read count of the cell `fp · o_C`. -/
  rC : F
  /-- The read count of the bytecode entry at `pc`. -/
  rbc : F
  deriving ProvableStruct

/-! ## Load-bearing lemmas -/

/-- Limb `i` of a sum is the sum of the limbs (CompPoly's `Ext.coeff_add`). -/
theorem limb_add (x y : E) (i : Fin 3) : (x + y).limb i = x.limb i + y.limb i :=
  CompPoly.Extension.Ext.coeff_add x y i

/-- The sum of two words, limb by limb: the result coordinates of the `XOR` table
(specification §7.1; `tables.rs:470-476`). -/
theorem add_limbs (a0 a1 a2 b0 b1 b2 : K) :
    E.ofLimbs a0 a1 a2 + E.ofLimbs b0 b1 b2 = E.ofLimbs (a0 + b0) (a1 + b1) (a2 + b2) :=
  E.ext fun i ↦ by rw [limb_add]; fin_cases i <;> simp

/-- The bytecode tuple of an `XOR` row is the entry of the instruction it names (Layer 4). -/
theorem xor_entry (oA oB oC : K) :
    #v[Opcode.xor.code] ++ #v[oA, oB, oC, 0, 0, 0, 0] = entry (.xor oA oB oC) := rfl

/-! ## The table -/

/-- The `XOR` table (specification §7.1; `tables.rs:436-528`): state step, bytecode read of
`(XOR, o_A, o_B, o_C, 0, 0, 0, 0)`, the two operand reads, and the result read carrying the
limb-wise sum. Returns the pushed successor `(g·pc, fp)`. -/
def xorTable : GeneralFormalCircuit K XorRow Regs where
  main r := do
    let next : Var Regs K := ⟨Expression.const g * r.pc, r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.xor.code) #v[r.oA, r.oB, r.oC, 0, 0, 0, 0]
    memRead (r.fp * r.oA) r.rA r.vA
    memRead (r.fp * r.oB) r.rB r.vB
    memRead (r.fp * r.oC) r.rC #v[r.vA[0] + r.vB[0], r.vA[1] + r.vB[1], r.vA[2] + r.vB[2]]
    pure next
  -- The push channels: their requirements are vacuous (Layer 5), the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Clean's default tactic decides channel equalities through `Channel.toRaw_ext_iff`, whose
    -- `-1 : K` core's `BitVec.reduceNeg` simproc then rewrites as the two's-complement word,
    -- which the kernel rejects (status finding E6); neither is needed here.
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The row is a step: from its registers the machine steps to the pushed successor.
  Spec r next data := step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next
  -- The honest row: the operands are the fetched instruction's, and the three reads, the sum
  -- included, are the image's words.
  ProverAssumptions r data _ :=
    (programOf data).fetch r.pc = some (.xor r.oA r.oB r.oC) ∧
    (imageOf data).2.read (r.fp * r.oA) = some (E.ofLimbs r.vA[0] r.vA[1] r.vA[2]) ∧
    (imageOf data).2.read (r.fp * r.oB) = some (E.ofLimbs r.vB[0] r.vB[1] r.vB[2]) ∧
    (imageOf data).2.read (r.fp * r.oC) =
      some (E.ofLimbs (r.vA[0] + r.vB[0]) (r.vA[1] + r.vB[1]) (r.vA[2] + r.vB[2]))
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, hA, hB, hC⟩ := h_holds
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    rw [xor_entry, decode_entry, Option.some.injEq] at hdec
    subst hdec
    simp only [Vector.getElem_map] at hA hB
    rw [step_of_fetch_eq_some hfetch]
    simp [execute, guard, hA, hB, hC, add_limbs, Regs.next]
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨hfetch, hA, hB, hC⟩ := h_assumptions
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    simp only [Vector.getElem_map] at hA hB hC ⊢
    exact ⟨⟨_, hfetch, by rw [xor_entry, decode_entry]⟩, hA, hB, hC⟩

end LeanerVM.Arithmetization
