/-
  LeanerVM.Arithmetization.Tables.MulNative

  The `MUL_NATIVE` table: one Clean component per row, sound and complete for the relation the
  row refines, its bindings to a program and an image together with Layer 3's `step`.
  A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Tables.Basic
import Clean.Circuit.Formal
import Clean.Utils.Tactics.CircuitProofStart

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

(`TOWER_LANES`; §7.2's `p_0 + p_3, p_1 + p_3 + p_4, p_2 + p_4`). Layer 0's `mul_limbs` is the
statement that these are the limbs of the product in `E`, and licenses the proofs to read the
result coordinates as `v_A · v_B` (roadmap acceptance test 9).

**The relation** is the `XOR` table's with the product for the sum (see
`LeanerVM.Arithmetization.Tables.Xor` for the template): `MulBindings prog mem r` binds the
instruction `MUL_NATIVE o_A o_B o_C` at `pc` (`fetch_eq`) and the two operand words
(`readA_eq`, `readB_eq`) to a program and an image; `MulRefines prog mem r next` is the
bindings and the step (`step_eq`); `mul_refines_iff` expands it to the word at `fp·o_C` being
the product of the two words in `E`, and the successor `(g·pc, fp)`. The public description of
the operation is the product in `E`; the circuit's expanded polynomial is `main`'s coordinates
alone, tied to it by `mul_limbs`. `MulSpec r next data` adapts the relation to Clean's prover
data and is the table's `Spec`; `ProverAssumptions r data _ := ∃ next, MulSpec r next data` is
the honest prover's row, proved of the row of any valid step by `mulRowOf_refines`
(`mul_step_complete`); completeness discharges the pulls from it through `mul_refines_iff` and
`mul_limbs`, the twelve products `main` emits being the product's limbs.

**The component** `mulTable` pulls the state `(pc, fp)`, pushes and returns the fall-through
successor `(g·pc, fp)`, reads the bytecode entry `(MUL, o_A, o_B, o_C, 0, 0, 0, 0)` at `pc`,
and reads the three cells `fp·o_A`, `fp·o_B`, `fp·o_C` with the third carrying the product.
`Spec` is `MulSpec`; soundness and completeness are as for `XOR`.

**Rows from steps.** `mulRowOf`, `mulRowOf_refines` and `mul_step_complete` are the `XOR`
statements for this table.

## Wrong readings excluded

* A five-lane or unfolded product is not the tower product: `y · y · y = y + 1`, so the
  `y^3` and `y^4` partial sums fold back into lanes `0, 1` and `1, 2` (acceptance test 9;
  `mul_limbs`, whose proof is exactly the fold by `y_pow_three`).
* `MulRefines` names the operands and the operand words: a wrong input limb fails the bindings
  even where the result cell happens to hold the product of the image's words.
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

/-! ## The relation -/

/-- The row's bindings to a program and an image: the instruction at `pc` is
`MUL_NATIVE o_A o_B o_C`, and the operand cells hold the row's words. -/
structure MulBindings {κ : ℕ} (prog : Program) (mem : MemImage κ) (r : MulRow K) : Prop where
  /-- The instruction at `pc` is `MUL_NATIVE o_A o_B o_C`. -/
  fetch_eq : prog.fetch r.pc = some (.mulNative r.oA r.oB r.oC)
  /-- The cell `fp · o_A` holds the row's word `v_A`. -/
  readA_eq : mem.read (r.fp * r.oA) = some (E.ofLimbs r.vA[0] r.vA[1] r.vA[2])
  /-- The cell `fp · o_B` holds the row's word `v_B`. -/
  readB_eq : mem.read (r.fp * r.oB) = some (E.ofLimbs r.vB[0] r.vB[1] r.vB[2])

/-- The relation a `MUL_NATIVE` row refines: it is bound to the program and the image, and from
its registers the machine steps to `next`. -/
structure MulRefines {κ : ℕ} (prog : Program) (mem : MemImage κ) (r : MulRow K) (next : Regs K) :
    Prop where
  /-- The row is bound to the program and the image. -/
  bindings : MulBindings prog mem r
  /-- From the row's registers the machine steps to `next`. -/
  step_eq : step prog mem ⟨r.pc, r.fp⟩ = some next

/-- `MulRefines`, expanded: the bindings, the result cell holds the product in `E`, and the
successor is the fall-through `(g·pc, fp)`. -/
theorem mul_refines_iff {κ : ℕ} (prog : Program) (mem : MemImage κ) (r : MulRow K)
    (next : Regs K) :
    MulRefines prog mem r next ↔
      MulBindings prog mem r ∧
        mem.read (r.fp * r.oC) =
          some (E.ofLimbs r.vA[0] r.vA[1] r.vA[2] * E.ofLimbs r.vB[0] r.vB[1] r.vB[2]) ∧
        next = Regs.next ⟨r.pc, r.fp⟩ := by
  constructor
  · rintro ⟨⟨hfetch, hA, hB⟩, hstep⟩
    refine ⟨⟨hfetch, hA, hB⟩, ?_⟩
    rw [step_of_fetch_eq_some hfetch] at hstep
    simp only [execute, hA, hB, Option.bind_eq_bind, Option.bind_some] at hstep
    cases hc : mem.read (r.fp * r.oC) with
    | none => rw [hc] at hstep; exact absurd hstep (by simp)
    | some c =>
      rw [hc, Option.bind_some, guard_bind_eq_some_iff] at hstep
      obtain ⟨rfl, h⟩ := hstep
      simp only [Option.pure_def, Option.some.injEq] at h
      exact ⟨rfl, h.symm⟩
  · rintro ⟨⟨hfetch, hA, hB⟩, hC, rfl⟩
    refine ⟨⟨hfetch, hA, hB⟩, ?_⟩
    rw [step_of_fetch_eq_some hfetch]
    simp only [execute, hA, hB, hC, Option.bind_eq_bind, Option.bind_some,
      guard_bind_eq_some_iff, Option.pure_def, true_and]

/-! ## The adapter to the prover data -/

/-- The table's `Spec`: the row refines `MulRefines` over the program and the image the prover
data names. -/
def MulSpec (r : MulRow K) (next : Regs K) (data : ProverData K) : Prop :=
  MulRefines (programOf data) (imageOf data).2 r next

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
  -- The row refines the relation over the data's program and image, to the pushed successor.
  Spec := MulSpec
  -- The honest prover's row: written from a valid step, it is bound and steps somewhere.
  -- Proved of the row built from any valid step by `mulRowOf_refines`; see
  -- `mul_step_complete`.
  ProverAssumptions r data _ := ∃ next, MulSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, hA, hB, hC⟩ := h_holds
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    -- The pulled tuple is the entry of `MUL_NATIVE` with the row's operands (Layer 4).
    obtain rfl := Option.some.inj ((decode_entry (.mulNative _ _ _)).symm.trans hdec)
    refine (mul_refines_iff _ _ _ _).mpr ⟨⟨hfetch, ?_, ?_⟩, ?_, rfl⟩
    · simpa only [Vector.getElem_map] using hA
    · simpa only [Vector.getElem_map] using hB
    · simpa only [mul_limbs, Vector.getElem_map] using hC
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The four pull guarantees, from the semantic premise: the tuple `main` emits is the
    -- fetched instruction's entry (Layer 4), and the result read carries the limbs of the
    -- product a valid step reads (`mul_limbs`).
    obtain ⟨next, h⟩ := h_assumptions
    obtain ⟨⟨hfetch, hA, hB⟩, hC, -⟩ := (mul_refines_iff _ _ _ _).mp h
    rw [mul_limbs] at hC
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    simp only [Vector.getElem_map] at hA hB hC ⊢
    exact ⟨⟨_, hfetch, decode_entry (.mulNative _ _ _)⟩, hA, hB, hC⟩

/-! ## Rows from steps -/

/-- The row of a step that fetches `MUL_NATIVE oA oB oC` from `(pc, fp)` over the image `mem`:
the registers, the operands, the two operand words read back from the image, and the counts
as parameters. Noncomputable: it reads the image. -/
noncomputable def mulRowOf {κ : ℕ} (mem : MemImage κ) (pc fp oA oB oC rA rB rC rbc : K) :
    MulRow K :=
  ⟨pc, fp, oA, oB, oC, mem.limbsAt (fp * oA), mem.limbsAt (fp * oB), rA, rB, rC, rbc⟩

/-- A valid step that fetches `MUL_NATIVE oA oB oC` is represented by `mulRowOf`, with any
counts: the honest prover's row refines the relation, which is `ProverAssumptions` over the
data. -/
theorem mulRowOf_refines {κ : ℕ} {prog : Program} {mem : MemImage κ} {pc fp oA oB oC : K}
    {next : Regs K} (hfetch : prog.fetch pc = some (.mulNative oA oB oC))
    (hstep : step prog mem ⟨pc, fp⟩ = some next) (rA rB rC rbc : K) :
    MulRefines prog mem (mulRowOf mem pc fp oA oB oC rA rB rC rbc) next := by
  have h := hstep
  rw [step_of_fetch_eq_some hfetch] at h
  simp only [execute, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, -⟩ := h
  refine ⟨⟨hfetch, ?_, ?_⟩, hstep⟩
  · show mem.read (fp * oA) = some (E.ofLimbs (mem.limbsAt (fp * oA))[0]
      (mem.limbsAt (fp * oA))[1] (mem.limbsAt (fp * oA))[2])
    rw [MemImage.ofLimbs_limbsAt ha]; exact ha
  · show mem.read (fp * oB) = some (E.ofLimbs (mem.limbsAt (fp * oB))[0]
      (mem.limbsAt (fp * oB))[1] (mem.limbsAt (fp * oB))[2])
    rw [MemImage.ofLimbs_limbsAt hb]; exact hb

/-- Every valid `MUL_NATIVE` step has a satisfying row, from the step alone: the constraints of
`main` hold of `mulRowOf` in the row environment over the data. -/
theorem mul_step_complete {data : ProverData K} {pc fp oA oB oC : K} {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.mulNative oA oB oC))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (rA rB rC rbc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((mulTable.main (const (mulRowOf (imageOf data).2 pc fp oA oB oC rA rB rC rbc))).operations
        0) :=
  (mulTable.completeness 0 (rowEnv data) (const _)
    -- No witness slot: the row environment uses the local witnesses vacuously.
    (by simp only [circuit_norm, mulTable, memRead, bytecodeRead, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover ⟨_, mulRowOf_refines hfetch hstep rA rB rC rbc⟩).1

end LeanerVM.Arithmetization
