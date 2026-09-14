/-
  LeanerVM.Arithmetization.Tables.Xor

  The `XOR` table: one Clean component per row, sound and complete for the row's functional
  specification, its bindings to the program and the image together with Layer 3's `step`.
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
`v_{A,i} + v_{B,i}`.

**The contract.** `XorRowBindings r data` binds the row to the program and the image named by
the prover data (Layer 5): the instruction at `pc` is `XOR o_A o_B o_C`, and the operand cells
`fp·o_A`, `fp·o_B` hold the row's words `word v_A`, `word v_B`. `XorSpec r next data` is the
bindings together with `step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next`, Layer 3's
`step` from the row's registers to `next`; `xor_spec_iff` expands it into the opcode's
equation, the word at `fp·o_C` is `word v_A + word v_B` in `E` (addition in `E`, whose limbs
are bitwise `XOR` in `K`, never integer addition), and the successor `next = (g·pc, fp)`;
`xor_spec_step` projects the step back out. `XorRowReads r data` is the four pull guarantees of
the row, the result read carrying the limb-wise sum: `xor_reads_iff` identifies it with the
semantic premise `∃ next, XorSpec r next data`, so a row is bound and steps exactly when its
pulls are reads of the data. Access counts are outside the contract: their allocation is the
bus's (Layers 8 and 9), and a wrong count does not falsify the opcode's specification.

**The component** `xorTable` pulls the state `(pc, fp)` and pushes the fall-through successor
`(g·pc, fp)` (`xor_output`), reads the bytecode entry `(XOR, o_A, o_B, o_C, 0, 0, 0, 0)` at
`pc`, and reads the three cells `fp·o_A`, `fp·o_B`, `fp·o_C` with the third carrying the sum.
It returns the pushed successor, and `Spec` is `XorSpec`.

**Soundness** assumes the guarantees of the four pulls (memory reads are the image's words,
the bytecode entry is the fetched instruction) and concludes `XorSpec`: the bindings are
exactly what the pulls guarantee, and the step follows by the arm of `execute`; the
requirements of the three pushes are vacuous, since the push channels guarantee nothing
(Layer 5: what a push must satisfy is this `Spec`). **Completeness** takes
`ProverAssumptions r data _ := ∃ next, XorSpec r next data`, the semantic premise, and
discharges each pull's guarantee from it through `xor_spec_iff`.

**Rows from steps.** `xorRowOf data pc fp oA oB oC rA rB rC rbc` is the row of a step: the
registers and the fetched operands, the two operand words read back from the image
(`limbsAt`), and the counts as parameters. `xorRowOf_spec` says it satisfies `XorSpec` whenever
the step is valid and fetches `XOR oA oB oC`, `xor_row_exists` is the existence statement, and
`xorRow_complete` pushes any row with the semantic premise through `completeness`: its
constraints hold in the row environment `rowEnv data`. The builder is noncomputable, since
`MemImage.read` is (Layer 2); an executable, data-aware generator is T2's, against these
theorems. Conversely `xor_reads_of_constraints` reads the four pull guarantees back off the
constraints `main` emits, for every environment.

## Wrong readings excluded

* The result is `v_A + v_B` limb by limb, in `E` (`add_limbs`): a row whose result read
  carries any other word fails `XorSpec`, since `step` compares the word read at `fp·o_C` with
  the sum (acceptance test: the mutated row in the tests).
* `XorSpec` names the row's operands and words, not only its registers: an `XOR` row at a
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

/-! ## The contract -/

/-- The row's bindings to the program and the image: the instruction at `pc` is
`XOR o_A o_B o_C`, and the operand cells hold the row's words. -/
def XorRowBindings (r : XorRow K) (data : ProverData K) : Prop :=
  (programOf data).fetch r.pc = some (.xor r.oA r.oB r.oC) ∧
  (imageOf data).2.read (r.fp * r.oA) = some (word r.vA) ∧
  (imageOf data).2.read (r.fp * r.oB) = some (word r.vB)

/-- The functional specification of an `XOR` row: it is bound to the program and the image,
and from its registers the machine steps to `next` (Layer 3's `step`). -/
def XorSpec (r : XorRow K) (next : Regs K) (data : ProverData K) : Prop :=
  XorRowBindings r data ∧ step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next

/-- The four pull guarantees of the row: the fetch and the three reads, the result read
carrying the limb-wise sum. The local completeness premise, what the row's pulls assume. -/
def XorRowReads (r : XorRow K) (data : ProverData K) : Prop :=
  (programOf data).fetch r.pc = some (.xor r.oA r.oB r.oC) ∧
  (imageOf data).2.read (r.fp * r.oA) = some (E.ofLimbs r.vA[0] r.vA[1] r.vA[2]) ∧
  (imageOf data).2.read (r.fp * r.oB) = some (E.ofLimbs r.vB[0] r.vB[1] r.vB[2]) ∧
  (imageOf data).2.read (r.fp * r.oC) =
    some (E.ofLimbs (r.vA[0] + r.vB[0]) (r.vA[1] + r.vB[1]) (r.vA[2] + r.vB[2]))

/-- `XorSpec`, expanded: the bindings, the result cell holds the sum in `E`, and the successor
is the fall-through `(g·pc, fp)`. -/
theorem xor_spec_iff (r : XorRow K) (next : Regs K) (data : ProverData K) :
    XorSpec r next data ↔
      XorRowBindings r data ∧
        (imageOf data).2.read (r.fp * r.oC) = some (word r.vA + word r.vB) ∧
        next = Regs.next ⟨r.pc, r.fp⟩ := by
  unfold XorSpec
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
theorem xor_spec_step {r : XorRow K} {next : Regs K} {data : ProverData K}
    (h : XorSpec r next data) : step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next :=
  h.2

/-- A row's pulls are reads of the data exactly when it is bound and steps: the local
completeness premise is the semantic one. -/
theorem xor_reads_iff (r : XorRow K) (data : ProverData K) :
    XorRowReads r data ↔ ∃ next, XorSpec r next data := by
  constructor
  · rintro ⟨hfetch, hA, hB, hC⟩
    exact ⟨_, (xor_spec_iff _ _ _).mpr ⟨⟨hfetch, hA, hB⟩, by rw [hC, word, word, add_limbs], rfl⟩⟩
  · rintro ⟨next, h⟩
    obtain ⟨⟨hfetch, hA, hB⟩, hC, -⟩ := (xor_spec_iff _ _ _).mp h
    rw [word, word, add_limbs] at hC
    exact ⟨hfetch, hA, hB, hC⟩

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
  -- The row is bound to the program and the image, and steps to the pushed successor.
  Spec := XorSpec
  -- The semantic premise: the row is bound and steps somewhere.
  ProverAssumptions r data _ := ∃ next, XorSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, hA, hB, hC⟩ := h_holds
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    rw [xor_entry, decode_entry, Option.some.injEq] at hdec
    subst hdec
    simp only [Vector.getElem_map] at hA hB hC
    refine ⟨⟨hfetch, ?_, ?_⟩, ?_⟩
    · simpa only [word, Vector.getElem_map] using hA
    · simpa only [word, Vector.getElem_map] using hB
    · rw [step_of_fetch_eq_some hfetch]
      simp [execute, guard, hA, hB, hC, add_limbs, Regs.next]
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨next, h⟩ := h_assumptions
    obtain ⟨⟨hfetch, hA, hB⟩, hC, -⟩ := (xor_spec_iff _ _ _).mp h
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    simp only [word, add_limbs, Vector.getElem_map] at hA hB hC ⊢
    exact ⟨⟨_, hfetch, by rw [xor_entry, decode_entry]⟩, hA, hB, hC⟩

/-- The returned successor: the fall-through `(g·pc, fp)`, for every environment. -/
theorem xor_output (env : Environment K) (offset : ℕ) (r : Var XorRow K) :
    eval env ((xorTable.main r).output offset) = ⟨g * (eval env r).pc, (eval env r).fp⟩ := by
  simp only [circuit_norm, xorTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The constraints `main` emits on a row are its four pull guarantees: read back off any
environment in which they hold. -/
theorem xor_reads_of_constraints {env : Environment K} {r : Var XorRow K} {offset : ℕ}
    (h : ConstraintsHold.Soundness env ((xorTable.main r).operations offset)) :
    XorRowReads (eval env r) env.data :=
  (xor_reads_iff _ _).mpr ⟨_, (xorTable.soundness offset env r (eval env r) rfl trivial h).1⟩

/-! ## Rows from steps -/

/-- The row of a step that fetches `XOR oA oB oC` from `(pc, fp)`: the registers, the operands,
the two operand words read back from the image, and the counts as parameters. Noncomputable:
it reads the image. -/
noncomputable def xorRowOf (data : ProverData K) (pc fp oA oB oC rA rB rC rbc : K) : XorRow K :=
  ⟨pc, fp, oA, oB, oC, limbsAt (imageOf data).2 (fp * oA), limbsAt (imageOf data).2 (fp * oB),
    rA, rB, rC, rbc⟩

/-- A valid step that fetches `XOR oA oB oC` is represented by `xorRowOf`, with any counts. -/
theorem xorRowOf_spec {data : ProverData K} {pc fp oA oB oC : K} {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.xor oA oB oC))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (rA rB rC rbc : K) :
    XorSpec (xorRowOf data pc fp oA oB oC rA rB rC rbc) next data := by
  have h := hstep
  rw [step_of_fetch_eq_some hfetch] at h
  simp only [execute, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, -⟩ := h
  refine ⟨⟨hfetch, ?_, ?_⟩, hstep⟩
  · show (imageOf data).2.read (fp * oA) = some (word (limbsAt (imageOf data).2 (fp * oA)))
    rw [word_limbsAt ha]; exact ha
  · show (imageOf data).2.read (fp * oB) = some (word (limbsAt (imageOf data).2 (fp * oB)))
    rw [word_limbsAt hb]; exact hb

/-- A valid step that fetches `XOR oA oB oC` admits a row with the same registers and
operands and any counts. -/
theorem xor_row_exists {data : ProverData K} {pc fp oA oB oC : K} {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.xor oA oB oC))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (rA rB rC rbc : K) :
    ∃ vA vB, XorSpec ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ next data :=
  ⟨_, _, xorRowOf_spec hfetch hstep rA rB rC rbc⟩

/-- A row with the semantic premise satisfies the constraints of `main` in the row environment
over its data: local completeness, literally. -/
theorem xorRow_complete {r : XorRow K} {data : ProverData K} (h : ∃ next, XorSpec r next data) :
    ConstraintsHold.Completeness (rowEnv data) ((xorTable.main (const r)).operations 0) :=
  (xorTable.completeness 0 (rowEnv data) (const r)
    (by simp only [circuit_norm, xorTable, memRead, bytecodeRead, -BitVec.reduceNeg]) r
    ProvableType.eval_const_prover h).1

end LeanerVM.Arithmetization
