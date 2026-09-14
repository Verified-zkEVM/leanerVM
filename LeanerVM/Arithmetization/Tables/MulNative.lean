/-
  LeanerVM.Arithmetization.Tables.MulNative

  The `MUL_NATIVE` table: one Clean component per row, sound and complete for the row's
  functional specification, its bindings to the program and the image together with Layer 3's
  `step`. A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Tables.Basic
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
that these are the limbs of the product in `E`, and licenses the proofs to read the result
coordinates as `v_A · v_B` (roadmap acceptance test 9).

**The contract** is the `XOR` table's with the product for the sum (see
`LeanerVM.Arithmetization.Tables.Xor` for the template): `MulRowBindings r data` binds the
instruction `MUL_NATIVE o_A o_B o_C` at `pc` and the two operand words; `MulSpec r next data`
is the bindings and the step; `mul_spec_iff` expands it to the word at `fp·o_C` being
`word v_A * word v_B`, the product in `E`, and the successor `(g·pc, fp)`; `mul_spec_step`
projects the step; `MulRowReads` is the four pull guarantees, the result read carrying the
twelve products, and `mul_reads_iff` identifies it with `∃ next, MulSpec r next data`. The
public description of the operation is the product in `E`; the circuit's expanded polynomial
is `main`'s coordinates alone, tied to it by `mul_limbs`.

**The component** `mulTable` pulls the state `(pc, fp)` and pushes the fall-through successor
`(g·pc, fp)` (`mul_output`), reads the bytecode entry `(MUL, o_A, o_B, o_C, 0, 0, 0, 0)` at
`pc`, and reads the three cells `fp·o_A`, `fp·o_B`, `fp·o_C` with the third carrying the
product. It returns the pushed successor, and `Spec` is `MulSpec`; soundness and completeness
are as for `XOR`, with `ProverAssumptions r data _ := ∃ next, MulSpec r next data`.

**Rows from steps.** `mulRowOf`, `mulRowOf_spec`, `mul_row_exists`, `mulRow_complete` and
`mul_reads_of_constraints` are the `XOR` statements for this table.

## Wrong readings excluded

* A five-lane or unfolded product is not the tower product: `y · y · y = y + 1`, so the
  `y^3` and `y^4` partial sums fold back into lanes `0, 1` and `1, 2` (acceptance test 9;
  `mul_limbs`, whose proof is exactly the fold by `y_pow_three`).
* `MulSpec` names the operands and the operand words: a wrong input limb fails the bindings
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

/-! ## The contract -/

/-- The row's bindings to the program and the image: the instruction at `pc` is
`MUL_NATIVE o_A o_B o_C`, and the operand cells hold the row's words. -/
def MulRowBindings (r : MulRow K) (data : ProverData K) : Prop :=
  (programOf data).fetch r.pc = some (.mulNative r.oA r.oB r.oC) ∧
  (imageOf data).2.read (r.fp * r.oA) = some (word r.vA) ∧
  (imageOf data).2.read (r.fp * r.oB) = some (word r.vB)

/-- The functional specification of a `MUL_NATIVE` row: it is bound to the program and the
image, and from its registers the machine steps to `next`. -/
def MulSpec (r : MulRow K) (next : Regs K) (data : ProverData K) : Prop :=
  MulRowBindings r data ∧ step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next

/-- The four pull guarantees of the row: the fetch and the three reads, the result read
carrying the twelve products. The local completeness premise. -/
def MulRowReads (r : MulRow K) (data : ProverData K) : Prop :=
  (programOf data).fetch r.pc = some (.mulNative r.oA r.oB r.oC) ∧
  (imageOf data).2.read (r.fp * r.oA) = some (E.ofLimbs r.vA[0] r.vA[1] r.vA[2]) ∧
  (imageOf data).2.read (r.fp * r.oB) = some (E.ofLimbs r.vB[0] r.vB[1] r.vB[2]) ∧
  (imageOf data).2.read (r.fp * r.oC) =
    some (E.ofLimbs (r.vA[0] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1])
      (r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1] +
        r.vA[2] * r.vB[2])
      (r.vA[0] * r.vB[2] + r.vA[1] * r.vB[1] + r.vA[2] * r.vB[0] + r.vA[2] * r.vB[2]))

/-- `MulSpec`, expanded: the bindings, the result cell holds the product in `E`, and the
successor is the fall-through `(g·pc, fp)`. -/
theorem mul_spec_iff (r : MulRow K) (next : Regs K) (data : ProverData K) :
    MulSpec r next data ↔
      MulRowBindings r data ∧
        (imageOf data).2.read (r.fp * r.oC) = some (word r.vA * word r.vB) ∧
        next = Regs.next ⟨r.pc, r.fp⟩ := by
  unfold MulSpec
  constructor
  · rintro ⟨⟨hfetch, hA, hB⟩, hstep⟩
    refine ⟨⟨hfetch, hA, hB⟩, ?_⟩
    rw [step_of_fetch_eq_some hfetch] at hstep
    simp only [execute, hA, hB, Option.bind_eq_bind, Option.bind_some] at hstep
    cases hc : (imageOf data).2.read (r.fp * r.oC) with
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

/-- The step, projected out of the specification. -/
theorem mul_spec_step {r : MulRow K} {next : Regs K} {data : ProverData K}
    (h : MulSpec r next data) : step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next :=
  h.2

/-- A row's pulls are reads of the data exactly when it is bound and steps. -/
theorem mul_reads_iff (r : MulRow K) (data : ProverData K) :
    MulRowReads r data ↔ ∃ next, MulSpec r next data := by
  constructor
  · rintro ⟨hfetch, hA, hB, hC⟩
    exact ⟨_, (mul_spec_iff _ _ _).mpr ⟨⟨hfetch, hA, hB⟩, by rw [hC, word, word, mul_limbs], rfl⟩⟩
  · rintro ⟨next, h⟩
    obtain ⟨⟨hfetch, hA, hB⟩, hC, -⟩ := (mul_spec_iff _ _ _).mp h
    rw [word, word, mul_limbs] at hC
    exact ⟨hfetch, hA, hB, hC⟩

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
  -- The row is bound to the program and the image, and steps to the pushed successor.
  Spec := MulSpec
  -- The semantic premise: the row is bound and steps somewhere.
  ProverAssumptions r data _ := ∃ next, MulSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, hA, hB, hC⟩ := h_holds
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    rw [mul_entry, decode_entry, Option.some.injEq] at hdec
    subst hdec
    refine (mul_spec_iff _ _ _).mpr ⟨⟨hfetch, ?_, ?_⟩, ?_, rfl⟩
    · simpa only [word, Vector.getElem_map] using hA
    · simpa only [word, Vector.getElem_map] using hB
    · simpa only [word, mul_limbs, Vector.getElem_map] using hC
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨hfetch, hA, hB, hC⟩ := (mul_reads_iff _ _).mpr h_assumptions
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    simp only [Vector.getElem_map] at hA hB hC ⊢
    exact ⟨⟨_, hfetch, by rw [mul_entry, decode_entry]⟩, hA, hB, hC⟩

/-- The returned successor: the fall-through `(g·pc, fp)`, for every environment. -/
theorem mul_output (env : Environment K) (offset : ℕ) (r : Var MulRow K) :
    eval env ((mulTable.main r).output offset) = ⟨g * (eval env r).pc, (eval env r).fp⟩ := by
  simp only [circuit_norm, mulTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The constraints `main` emits on a row are its four pull guarantees. -/
theorem mul_reads_of_constraints {env : Environment K} {r : Var MulRow K} {offset : ℕ}
    (h : ConstraintsHold.Soundness env ((mulTable.main r).operations offset)) :
    MulRowReads (eval env r) env.data :=
  (mul_reads_iff _ _).mpr ⟨_, (mulTable.soundness offset env r (eval env r) rfl trivial h).1⟩

/-! ## Rows from steps -/

/-- The row of a step that fetches `MUL_NATIVE oA oB oC` from `(pc, fp)`: the registers, the
operands, the two operand words read back from the image, and the counts as parameters.
Noncomputable: it reads the image. -/
noncomputable def mulRowOf (data : ProverData K) (pc fp oA oB oC rA rB rC rbc : K) : MulRow K :=
  ⟨pc, fp, oA, oB, oC, limbsAt (imageOf data).2 (fp * oA), limbsAt (imageOf data).2 (fp * oB),
    rA, rB, rC, rbc⟩

/-- A valid step that fetches `MUL_NATIVE oA oB oC` is represented by `mulRowOf`, with any
counts. -/
theorem mulRowOf_spec {data : ProverData K} {pc fp oA oB oC : K} {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.mulNative oA oB oC))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (rA rB rC rbc : K) :
    MulSpec (mulRowOf data pc fp oA oB oC rA rB rC rbc) next data := by
  have h := hstep
  rw [step_of_fetch_eq_some hfetch] at h
  simp only [execute, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, -⟩ := h
  refine ⟨⟨hfetch, ?_, ?_⟩, hstep⟩
  · show (imageOf data).2.read (fp * oA) = some (word (limbsAt (imageOf data).2 (fp * oA)))
    rw [word_limbsAt ha]; exact ha
  · show (imageOf data).2.read (fp * oB) = some (word (limbsAt (imageOf data).2 (fp * oB)))
    rw [word_limbsAt hb]; exact hb

/-- A valid step that fetches `MUL_NATIVE oA oB oC` admits a row with the same registers and
operands and any counts. -/
theorem mul_row_exists {data : ProverData K} {pc fp oA oB oC : K} {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.mulNative oA oB oC))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (rA rB rC rbc : K) :
    ∃ vA vB, MulSpec ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ next data :=
  ⟨_, _, mulRowOf_spec hfetch hstep rA rB rC rbc⟩

/-- A row with the semantic premise satisfies the constraints of `main` in the row environment
over its data. -/
theorem mulRow_complete {r : MulRow K} {data : ProverData K} (h : ∃ next, MulSpec r next data) :
    ConstraintsHold.Completeness (rowEnv data) ((mulTable.main (const r)).operations 0) :=
  (mulTable.completeness 0 (rowEnv data) (const r)
    (by simp only [circuit_norm, mulTable, memRead, bytecodeRead, -BitVec.reduceNeg]) r
    ProvableType.eval_const_prover h).1

end LeanerVM.Arithmetization
