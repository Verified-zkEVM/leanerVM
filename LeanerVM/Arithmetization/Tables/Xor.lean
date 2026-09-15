/-
  LeanerVM.Arithmetization.Tables.Xor

  The `XOR` table: one Clean component per row, sound and complete for the relation the row
  refines, its bindings to a program and an image together with Layer 3's `step`.
  A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Tables.Basic
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
`v_{A,i} + v_{B,i}`. A three-limb column `v` is the word `E.ofLimbs v[0] v[1] v[2]`, as Layer
5's `MemPull.Guarantees` spells it.

**The relation.** `XorBindings prog mem r` binds the row to a program and an image, as named
facts: `fetch_eq`, the instruction at `pc` is `XOR o_A o_B o_C`; `readA_eq`, `readB_eq`, the
operand cells `fp·o_A`, `fp·o_B` hold the row's words. `XorRefines prog mem r next` is the
bindings together with `step_eq : step prog mem ⟨pc, fp⟩ = some next`, Layer 3's `step` from
the row's registers to `next`: the relation an `XOR` row refines, stated over the program and
the image themselves, so that execution and witness proofs state their obligations over
theirs. `xor_refines_iff` expands it into the opcode's equation, the word at `fp·o_C` is the
sum of the two words in `E` (addition in `E`, whose limbs are bitwise `XOR` in `K`, never
integer addition), and the successor `next = (g·pc, fp)`. Access counts are outside the
relation: their allocation is the bus's (Layers 8 and 9), and a wrong count does not falsify
the opcode's specification.

**The adapter.** `XorSpec r next data := XorRefines (programOf data) (imageOf data).2 r next`
reads the program and the image off Clean's prover data (Layer 5) and is the table's `Spec`;
constructing and relating `ProverData` is this one explicit step. The row's pull guarantees
have no name of their own: they are what Clean's `circuit_proof_start` hands soundness as
hypotheses and asks of completeness as goals, and `xor_refines_iff` with Layer 0's `add_limbs`
is their semantic reading (the result read carries the sum's limbs).

**The component** `xorTable` pulls the state `(pc, fp)`, pushes and returns the fall-through
successor `(g·pc, fp)`, reads the bytecode entry `(XOR, o_A, o_B, o_C, 0, 0, 0, 0)` at `pc`,
and reads the three cells `fp·o_A`, `fp·o_B`, `fp·o_C` with the third carrying the sum. `Spec`
is `XorSpec`.

**Soundness** assumes the guarantees of the four pulls (memory reads are the image's words,
the bytecode entry is the fetched instruction, which Layer 4's `decode_entry` identifies with
`XOR o_A o_B o_C`) and concludes `XorSpec`: the bindings are exactly what the pulls guarantee,
and the step follows by the arm of `execute`; the requirements of the three pushes are vacuous,
since the push channels guarantee nothing (Layer 5: what a push must satisfy is this `Spec`).

**Completeness** takes `ProverAssumptions r data _ := ∃ next, XorSpec r next data`: the row is
an honest row, one an honest prover wrote from a valid step of the execution it proves, so it
is bound to the program and the image and the machine steps from its registers. That is the
honest-prover precondition Clean's completeness is relative to, and nothing above this file
assumes it: `xorRowOf_refines` proves it of the row built from any valid `XOR` step, so
`xor_step_complete` states completeness from the step alone. What completeness then proves is
the encoding: the tuple `main` emits decodes to the fetched instruction (Layer 4's
`decode_entry`), and the coordinates it emits for the result read are the limbs of the word a
valid step reads (`add_limbs`, through `xor_refines_iff`); a mistranscribed lane would fail
here. For a table without constraints the constraints are the pull guarantees and nothing
else, which is why the proof is a substitution once `xor_refines_iff` and `add_limbs` have
done theirs.

**Rows from steps.** `xorRowOf mem pc fp oA oB oC rA rB rC rbc` is the row of a step over the
image `mem`: the registers and the fetched operands, the two operand words read back from the
image (`MemImage.limbsAt`, Layer 2), and the counts as parameters. `xorRowOf_refines` says it
refines `XorRefines prog mem` whenever the step is valid and fetches `XOR oA oB oC`, and
`xor_step_complete` pushes it through `completeness` over the prover data: every valid `XOR`
step has a satisfying row, its constraints holding in the row environment `rowEnv data`. The
builder is noncomputable, since `MemImage.read` is; an executable, data-aware generator is
T2's, against these theorems.

This is all a table file states. Facts about its bytecode tuple are Layer 4's (`decode_entry`),
the successor `main` returns is fixed by `xor_refines_iff` under `soundness`, and one-line
corollaries of `soundness` and `completeness` are left to their consumers.

## Wrong readings excluded

* The result is `v_A + v_B` limb by limb, in `E` (`add_limbs`): a row whose result read
  carries any other word fails `XorRefines`, since `step` compares the word read at `fp·o_C`
  with the sum (acceptance test: the mutated row in the tests).
* `XorRefines` names the row's operands and words, not only its registers: an `XOR` row at a
  counter that fetches another instruction, or with an operand word that is not the image's,
  fails its bindings even where `step` succeeds (the review's counterexamples, in the tests).
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

/-! ## The relation -/

/-- The row's bindings to a program and an image: the instruction at `pc` is `XOR o_A o_B o_C`,
and the operand cells hold the row's words. -/
structure XorBindings {κ : ℕ} (prog : Program) (mem : MemImage κ) (r : XorRow K) : Prop where
  /-- The instruction at `pc` is `XOR o_A o_B o_C`. -/
  fetch_eq : prog.fetch r.pc = some (.xor r.oA r.oB r.oC)
  /-- The cell `fp · o_A` holds the row's word `v_A`. -/
  readA_eq : mem.read (r.fp * r.oA) = some (E.ofLimbs r.vA[0] r.vA[1] r.vA[2])
  /-- The cell `fp · o_B` holds the row's word `v_B`. -/
  readB_eq : mem.read (r.fp * r.oB) = some (E.ofLimbs r.vB[0] r.vB[1] r.vB[2])

/-- The relation an `XOR` row refines: it is bound to the program and the image, and from its
registers the machine steps to `next` (Layer 3's `step`). -/
structure XorRefines {κ : ℕ} (prog : Program) (mem : MemImage κ) (r : XorRow K) (next : Regs K) :
    Prop where
  /-- The row is bound to the program and the image. -/
  bindings : XorBindings prog mem r
  /-- From the row's registers the machine steps to `next`. -/
  step_eq : step prog mem ⟨r.pc, r.fp⟩ = some next

/-- `XorRefines`, expanded: the bindings, the result cell holds the sum in `E`, and the
successor is the fall-through `(g·pc, fp)`. -/
theorem xor_refines_iff {κ : ℕ} (prog : Program) (mem : MemImage κ) (r : XorRow K)
    (next : Regs K) :
    XorRefines prog mem r next ↔
      XorBindings prog mem r ∧
        mem.read (r.fp * r.oC) =
          some (E.ofLimbs r.vA[0] r.vA[1] r.vA[2] + E.ofLimbs r.vB[0] r.vB[1] r.vB[2]) ∧
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

/-- The table's `Spec`: the row refines `XorRefines` over the program and the image the prover
data names (Layer 5's `programOf`, `imageOf`). -/
def XorSpec (r : XorRow K) (next : Regs K) (data : ProverData K) : Prop :=
  XorRefines (programOf data) (imageOf data).2 r next

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
  -- The row refines the relation over the data's program and image, to the pushed successor.
  Spec := XorSpec
  -- The honest prover's row: written from a valid step, it is bound and steps somewhere.
  -- Proved of the row built from any valid step by `xorRowOf_refines`; see
  -- `xor_step_complete`.
  ProverAssumptions r data _ := ∃ next, XorSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, hA, hB, hC⟩ := h_holds
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    -- The pulled tuple is the entry of `XOR` with the row's operands (Layer 4).
    obtain rfl := Option.some.inj ((decode_entry (.xor _ _ _)).symm.trans hdec)
    refine (xor_refines_iff _ _ _ _).mpr ⟨⟨hfetch, ?_, ?_⟩, ?_, rfl⟩
    · simpa only [Vector.getElem_map] using hA
    · simpa only [Vector.getElem_map] using hB
    · simpa only [add_limbs, Vector.getElem_map] using hC
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The four pull guarantees, from the semantic premise: the tuple `main` emits is the
    -- fetched instruction's entry (Layer 4), and the result read carries the limbs of the sum
    -- a valid step reads (`add_limbs`).
    obtain ⟨next, h⟩ := h_assumptions
    obtain ⟨⟨hfetch, hA, hB⟩, hC, -⟩ := (xor_refines_iff _ _ _ _).mp h
    rw [add_limbs] at hC
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    simp only [Vector.getElem_map] at hA hB hC ⊢
    exact ⟨⟨_, hfetch, decode_entry (.xor _ _ _)⟩, hA, hB, hC⟩

/-! ## Rows from steps -/

/-- The row of a step that fetches `XOR oA oB oC` from `(pc, fp)` over the image `mem`: the
registers, the operands, the two operand words read back from the image, and the counts as
parameters. Noncomputable: it reads the image. -/
noncomputable def xorRowOf {κ : ℕ} (mem : MemImage κ) (pc fp oA oB oC rA rB rC rbc : K) :
    XorRow K :=
  ⟨pc, fp, oA, oB, oC, mem.limbsAt (fp * oA), mem.limbsAt (fp * oB), rA, rB, rC, rbc⟩

/-- A valid step that fetches `XOR oA oB oC` is represented by `xorRowOf`, with any counts: the
honest prover's row refines the relation, which is `ProverAssumptions` over the data. -/
theorem xorRowOf_refines {κ : ℕ} {prog : Program} {mem : MemImage κ} {pc fp oA oB oC : K}
    {next : Regs K} (hfetch : prog.fetch pc = some (.xor oA oB oC))
    (hstep : step prog mem ⟨pc, fp⟩ = some next) (rA rB rC rbc : K) :
    XorRefines prog mem (xorRowOf mem pc fp oA oB oC rA rB rC rbc) next := by
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

/-- Every valid `XOR` step has a satisfying row, from the step alone: the constraints of `main`
hold of `xorRowOf` in the row environment over the data. -/
theorem xor_step_complete {data : ProverData K} {pc fp oA oB oC : K} {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.xor oA oB oC))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (rA rB rC rbc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((xorTable.main (const (xorRowOf (imageOf data).2 pc fp oA oB oC rA rB rC rbc))).operations
        0) :=
  (xorTable.completeness 0 (rowEnv data) (const _)
    -- No witness slot: the row environment uses the local witnesses vacuously.
    (by simp only [circuit_norm, xorTable, memRead, bytecodeRead, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover ⟨_, xorRowOf_refines hfetch hstep rA rB rC rbc⟩).1

end LeanerVM.Arithmetization
