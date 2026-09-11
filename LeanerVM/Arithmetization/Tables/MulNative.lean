/-
  LeanerVM.Arithmetization.Tables.MulNative

  The `MUL_NATIVE` table: one Clean component per row, sound and complete for `step`.
  A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Channels
import Clean.Circuit.Formal
import Clean.Utils.Tactics.CircuitProofStart
import Mathlib.Tactic.LinearCombination

/-!
# The `MUL_NATIVE` table

leanISA roadmap Layer 6 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `93c9d1ef`. Category B: the columns
are `crates/lean_vm/src/tables.rs:436-455` (`mod arith`, shared with `XOR`, in that order), the
flushes `tables.rs:487-500` (`Arith::flushes` with `is_xor = false`), the result coordinates
`tables.rs:44-49` and `:478-480` (`TOWER_LANES`, `arith_result`), all matching specification
§7.2 (`doc/leanvm/body/07-instruction-tables.tex:28-50`). There is no constraint: the bus
balance is the assertion `[o_C] = [o_A] · [o_B]` (§5, "M3").

**The row** `MulRow` is the column list: `pc, fp`; the operands `o_A, o_B, o_C`; the two read
words `v_A, v_B` as three limbs each; the memory counts `r_A, r_B, r_C`; the bytecode count
`r_bc`. The product is never a column: its limbs ride the third memory read as the twelve
products over the nine limb pairs, folded by `y^3 = y + 1` into three lanes,

```text
c0 = a0·b0 + a1·b2 + a2·b1
c1 = a0·b1 + a1·b0 + a1·b2 + a2·b1 + a2·b2
c2 = a0·b2 + a1·b1 + a2·b0 + a2·b2
```

(`TOWER_LANES`; §7.2's `p_0 + p_3, p_1 + p_3 + p_4, p_2 + p_4`). `mul_limbs` is the statement
that these are the limbs of the product in `E`, and licenses the soundness proof to read the
result coordinates as `v_A · v_B` (roadmap acceptance test 9).

**The component** `mulTable` pulls the state `(pc, fp)` and pushes the fall-through successor
`(g·pc, fp)`, reads the bytecode entry `(MUL, o_A, o_B, o_C, 0, 0, 0, 0)` at `pc`, and reads the
three cells `fp·o_A`, `fp·o_B`, `fp·o_C` with the third carrying the product. It returns the
pushed successor, and `Spec` is `step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next`
(see `LeanerVM.Arithmetization.Tables.Xor` for the template).

## Wrong readings excluded

* A five-lane or unfolded product is not the tower product: `y · y · y = y + 1`, so the
  `y^3` and `y^4` partial sums fold back into lanes `0, 1` and `1, 2` (acceptance test 9;
  `mul_limbs`, whose proof is exactly the fold by `y_pow_three`).
* The successor is `(g·pc, fp)` (acceptance test 3); the spare bytecode slots are literal
  zeros (status finding R24).
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

/-! ## The row -/

/-- The `MUL_NATIVE` columns, in the order of `tables.rs:436-455`. -/
structure MulRow (F : Type) where
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

/-- `ofK` preserves sums: it is `algebraMap K E`. -/
theorem ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

/-- `ofK` preserves products: it is `algebraMap K E`. -/
theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

/-- The product of two words, limb by limb: the twelve products over the nine limb pairs,
folded by `y^3 = y + 1` (specification §7.2; `tables.rs:44-49`, `TOWER_LANES`). -/
theorem mul_limbs (a0 a1 a2 b0 b1 b2 : K) :
    E.ofLimbs a0 a1 a2 * E.ofLimbs b0 b1 b2 =
      E.ofLimbs (a0 * b0 + a1 * b2 + a2 * b1)
        (a0 * b1 + a1 * b0 + a1 * b2 + a2 * b1 + a2 * b2)
        (a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2) := by
  simp only [ofLimbs_eq, ofK_add, ofK_mul]
  -- The product is `p₀ + p₁·y + p₂·y² + p₃·y³ + p₄·y⁴`; `y³ = y + 1` folds `p₃` and `p₄`.
  linear_combination (ofK a1 * ofK b2 + ofK a2 * ofK b1 + ofK a2 * ofK b2 * y) * y_pow_three

/-- The bytecode tuple of a `MUL_NATIVE` row is the entry of the instruction it names (Layer 4). -/
theorem mul_entry (oA oB oC : K) :
    #v[Opcode.mulNative.code] ++ #v[oA, oB, oC, 0, 0, 0, 0] = entry (.mulNative oA oB oC) := rfl

/-! ## The table -/

/-- The `MUL_NATIVE` table (specification §7.2; `tables.rs:436-528`): state step, bytecode read
of `(MUL, o_A, o_B, o_C, 0, 0, 0, 0)`, the two operand reads, and the result read carrying the
tower product's three lanes. Returns the pushed successor `(g·pc, fp)`. -/
def mulTable : GeneralFormalCircuit K MulRow Regs where
  main r := do
    let next : Var Regs K := ⟨Expression.const g * r.pc, r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.mulNative.code)
      #v[r.oA, r.oB, r.oC, 0, 0, 0, 0]
    memRead (r.fp * r.oA) r.rA r.vA
    memRead (r.fp * r.oB) r.rB r.vB
    -- `TOWER_LANES` (`tables.rs:44-49`), lane by lane, pair by pair.
    memRead (r.fp * r.oC) r.rC
      #v[r.vA[0] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1],
         r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1] +
           r.vA[2] * r.vB[2],
         r.vA[0] * r.vB[2] + r.vA[1] * r.vB[1] + r.vA[2] * r.vB[0] + r.vA[2] * r.vB[2]]
    pure next
  -- The push channels: their requirements are vacuous (Layer 5), the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Without core's `BitVec.reduceNeg` simproc, which misreads `-1 : K` (finding E6).
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The row is a step: from its registers the machine steps to the pushed successor.
  Spec r next data := step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next
  -- The honest row: the operands are the fetched instruction's, and the three reads, the
  -- product included, are the image's words.
  ProverAssumptions r data _ :=
    (programOf data).fetch r.pc = some (.mulNative r.oA r.oB r.oC) ∧
    (imageOf data).2.read (r.fp * r.oA) = some (E.ofLimbs r.vA[0] r.vA[1] r.vA[2]) ∧
    (imageOf data).2.read (r.fp * r.oB) = some (E.ofLimbs r.vB[0] r.vB[1] r.vB[2]) ∧
    (imageOf data).2.read (r.fp * r.oC) =
      some (E.ofLimbs (r.vA[0] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1])
        (r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1] +
          r.vA[2] * r.vB[2])
        (r.vA[0] * r.vB[2] + r.vA[1] * r.vB[1] + r.vA[2] * r.vB[0] + r.vA[2] * r.vB[2]))
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, hA, hB, hC⟩ := h_holds
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    rw [mul_entry, decode_entry, Option.some.injEq] at hdec
    subst hdec
    simp only [Vector.getElem_map] at hA hB
    rw [step_of_fetch_eq_some hfetch]
    simp [execute, guard, hA, hB, hC, mul_limbs, Regs.next]
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨hfetch, hA, hB, hC⟩ := h_assumptions
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    simp only [Vector.getElem_map] at hA hB hC ⊢
    exact ⟨⟨_, hfetch, by rw [mul_entry, decode_entry]⟩, hA, hB, hC⟩

end LeanerVM.Arithmetization
