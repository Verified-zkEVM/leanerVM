/-
  LeanerVM.Arithmetization.Tables.Blake2s

  The `BLAKE2S` table: one Clean component per row, sound and complete for the row's
  functional specification, its bindings to the program and the image together with Layer 3's
  `step`, under the named assumption that Flock proves the compression relation on the row's
  eighteen limbs. A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Tables.Basic
import Clean.Circuit.Formal
import Clean.Utils.Tactics.CircuitProofStart

/-!
# The `BLAKE2S` table

leanISA roadmap Layer 6 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `93c9d1ef`. Category B: the columns
are `crates/lean_vm/src/tables.rs:846-882` (`mod blake2st`, in that order), the flushes
`tables.rs:889-921` (`Blake2sTable::flushes`), matching specification §7.6
(`doc/leanvm/body/07-instruction-tables.tex:114-141`). There is no table constraint: the
compression relation is proved by Flock on the eighteen limbs committed to `q_flock`.

**The row** `Blake2sRow` is the column list: `pc, fp`; the operands `o_{m₀}, …, o_{m₃}, o_cv,
o_out, o_md`; the eighteen limbs, two per cell, in the Rust order (the four message cells, the
output pair, the chaining-value pair, the metadata cell); one memory count per cell; the
bytecode count `r_bc`. Every cell is canonical: its top limb is a literal zero on the bus
(`memory_128`, `tables.rs:180-182`), never a column.

**The contract.** `Blake2sRowBindings r data` binds the row to the program and the image: the
instruction at `pc` is `BLAKE2S [o_{m₀}, …, o_{m₃}] o_cv o_out o_md` with the row's seven
operands, and the nine cells `fp·o_{mᵢ}`, `fp·o_cv`, `fp·(g·o_cv)`, `fp·o_out`, `fp·(g·o_out)`,
`fp·o_md` hold the row's canonical cells `E.ofCell mᵢ`, `E.ofCell cv₀`, `E.ofCell cv₁`, `E.ofCell
out₀`, `E.ofCell out₁`, `E.ofCell md`. `Blake2sSpec r next data` is the bindings and the step;
`blake2s_spec_iff` expands it: the bindings, `Blake2sRelation r` (the compression on the nine
cells, counter and both finalization flags included, through Layer 1's `CompressCells`), and
the successor `(g·pc, fp)`.

**The boundary.** `Blake2sRelation r` stays the `Assumptions` field: the component proves the
memory and bytecode binding, and Flock (issue #3) discharges the compression for the composed
system. Soundness of `Blake2sSpec` is conditional on it, never unconditional; nothing here
re-proves or re-states the compression. Local completeness takes `ProverAssumptions r data _
:= Blake2sRowBindings r data`, the ten pull guarantees: it accepts any correctly bound
canonical cells without checking the compression, which is what a bound row with a wrong but
canonical output exhibits (`blake2sRow_complete`, the boundary stated; the tests). The semantic
premise `∃ next, Blake2sSpec r next data` implies the bindings (`blake2s_spec_iff`), so it also
drives completeness (`blake2s_step_complete`).

**The component** `blake2sTable` pulls the state `(pc, fp)`, pushes and returns `(g·pc, fp)`,
reads the bytecode entry `(B2S, o_{m₀}, o_{m₁}, o_{m₂}, o_{m₃}, o_cv, o_out, o_md)` at `pc`
(the fetched instruction, by Layer 4's `decode_entry`), and reads the nine cells in the order of
§7.6, each as `(lo, hi, 0)`. `Spec` is `Blake2sSpec`.

**Rows from steps.** `blake2sRowOf` reads the nine cells back from the image
(`MemImage.cellAt`, Layer 2: the two limbs of a canonical word), and `blake2sRowOf_spec` says
it satisfies `Blake2sSpec` whenever the step is valid: `CompressCells` makes every cell
canonical, which is what reading two limbs back needs. `blake2s_step_complete` is its acceptance
by `main`, from the step alone (see `LeanerVM.Arithmetization.Tables.Xor` for the template).

## Wrong readings excluded

* All nine cells are canonical, the two output cells included (roadmap acceptance test 12):
  every memory read carries a literal zero top limb, so an image word with a nonzero top limb
  cannot balance the bus (the mutated row in the tests).
* The second cell of each pair is at `g·fp·o`, a free `×g` on the product coordinate
  (`Prod(FP, O_CV, 1)`), matching `execute`'s `fp · (g · o_cv)`.
* The two finalization flags are the two words of the metadata cell's limb `1`, entering
  `compress` unchanged (Layer 1, acceptance test 10); the table constrains nothing about them.
* Binding is not compression: a row whose output cells hold a canonical word that is not the
  compression is bound, locally complete, and fails `Blake2sRelation` and `Blake2sSpec`; that
  failure is Flock's to enforce (the boundary test).
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

/-! ## The row -/

/-- The `BLAKE2S` columns, in the order of `tables.rs:846-882`: a cell's two limbs `(lo, hi)`
are a `Vector F 2`. -/
structure Blake2sRow (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operand `o_{m₀}`. -/
  om0 : F
  /-- The operand `o_{m₁}`. -/
  om1 : F
  /-- The operand `o_{m₂}`. -/
  om2 : F
  /-- The operand `o_{m₃}`. -/
  om3 : F
  /-- The operand `o_cv`, the chaining-value base. -/
  ocv : F
  /-- The operand `o_out`, the output base. -/
  oout : F
  /-- The operand `o_md`, the metadata cell. -/
  omd : F
  /-- Message cell `0`, two limbs. -/
  m0 : Vector F 2
  /-- Message cell `1`. -/
  m1 : Vector F 2
  /-- Message cell `2`. -/
  m2 : Vector F 2
  /-- Message cell `3`. -/
  m3 : Vector F 2
  /-- Output cell `0`. -/
  out0 : Vector F 2
  /-- Output cell `1`. -/
  out1 : Vector F 2
  /-- Chaining-value cell `0`. -/
  cv0 : Vector F 2
  /-- Chaining-value cell `1`. -/
  cv1 : Vector F 2
  /-- The metadata cell: the counter, and the two flag words. -/
  md : Vector F 2
  /-- The read counts of the four message cells. -/
  rm0 : F
  rm1 : F
  rm2 : F
  rm3 : F
  /-- The read counts of the two chaining-value cells. -/
  rcv0 : F
  rcv1 : F
  /-- The read counts of the two output cells. -/
  rout0 : F
  rout1 : F
  /-- The read count of the metadata cell. -/
  rmd : F
  /-- The read count of the bytecode entry at `pc`. -/
  rbc : F
  deriving ProvableStruct

/-- The compression relation on a row's eighteen limbs, as Flock proves it (issue #3):
Layer 1's `CompressCells` on the nine canonical cells. The named assumption of the table. -/
def Blake2sRelation (r : Blake2sRow K) : Prop :=
  CompressCells ![E.ofCell r.m0, E.ofCell r.m1, E.ofCell r.m2, E.ofCell r.m3] (E.ofCell r.cv0)
    (E.ofCell r.cv1) (E.ofCell r.out0) (E.ofCell r.out1) (E.ofCell r.md)

/-! ## Proof helper -/

/-- The bytecode tuple of a `BLAKE2S` row is Layer 4's `entry` of the instruction it names, by
definition. Spelled once, privately: with the four message operands packed as a `Fin 4 → K`
vector, the unifier does not see this through `decode` on its own (it times out at `whnf`),
where the other tables' tuples unify against `decode_entry` directly. -/
private theorem blake2s_entry (om0 om1 om2 om3 ocv oout omd : K) :
    #v[Opcode.blake2s.code] ++ #v[om0, om1, om2, om3, ocv, oout, omd] =
      entry (.blake2s ![om0, om1, om2, om3] ocv oout omd) := rfl

/-! ## The contract -/

/-- The row's bindings to the program and the image: the instruction at `pc` is `BLAKE2S` with
the row's operands, and the nine cells hold the row's canonical cells. -/
def Blake2sRowBindings (r : Blake2sRow K) (data : ProverData K) : Prop :=
  (programOf data).fetch r.pc =
    some (.blake2s ![r.om0, r.om1, r.om2, r.om3] r.ocv r.oout r.omd) ∧
  (imageOf data).2.read (r.fp * r.om0) = some (E.ofCell r.m0) ∧
  (imageOf data).2.read (r.fp * r.om1) = some (E.ofCell r.m1) ∧
  (imageOf data).2.read (r.fp * r.om2) = some (E.ofCell r.m2) ∧
  (imageOf data).2.read (r.fp * r.om3) = some (E.ofCell r.m3) ∧
  (imageOf data).2.read (r.fp * r.ocv) = some (E.ofCell r.cv0) ∧
  (imageOf data).2.read (r.fp * (g * r.ocv)) = some (E.ofCell r.cv1) ∧
  (imageOf data).2.read (r.fp * r.oout) = some (E.ofCell r.out0) ∧
  (imageOf data).2.read (r.fp * (g * r.oout)) = some (E.ofCell r.out1) ∧
  (imageOf data).2.read (r.fp * r.omd) = some (E.ofCell r.md)

/-- The functional specification of a `BLAKE2S` row: it is bound to the program and the image,
and from its registers the machine steps to `next`. -/
def Blake2sSpec (r : Blake2sRow K) (next : Regs K) (data : ProverData K) : Prop :=
  Blake2sRowBindings r data ∧ step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next

/-- `Blake2sSpec`, expanded: the bindings, the compression relation on the row's cells, and the
successor is the fall-through `(g·pc, fp)`. -/
theorem blake2s_spec_iff (r : Blake2sRow K) (next : Regs K) (data : ProverData K) :
    Blake2sSpec r next data ↔
      Blake2sRowBindings r data ∧ Blake2sRelation r ∧ next = Regs.next ⟨r.pc, r.fp⟩ := by
  unfold Blake2sSpec
  constructor
  · rintro ⟨⟨hfetch, hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩, hstep⟩
    refine ⟨⟨hfetch, hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩, ?_⟩
    rw [step_of_fetch_eq_some hfetch] at hstep
    simp only [execute, hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd, Matrix.cons_val,
      Fin.isValue, Option.bind_eq_bind, Option.bind_some, guard_bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hstep
    exact ⟨hstep.1, hstep.2.symm⟩
  · rintro ⟨⟨hfetch, hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩, hrel, rfl⟩
    refine ⟨⟨hfetch, hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩, ?_⟩
    unfold Blake2sRelation at hrel
    rw [step_of_fetch_eq_some hfetch]
    simp only [execute, hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd, Matrix.cons_val,
      Fin.isValue, Option.bind_eq_bind, Option.bind_some, guard_bind_eq_some_iff, hrel,
      true_and, Option.pure_def]

/-! ## The table -/

/-- The `BLAKE2S` table (specification §7.6; `tables.rs:846-960`): state step, bytecode read of
`(B2S, o_{m₀}, …, o_md)`, and the nine canonical cell reads. Returns the pushed successor
`(g·pc, fp)`; sound under `Blake2sRelation`. -/
def blake2sTable : GeneralFormalCircuit K Blake2sRow Regs where
  main r := do
    let next : Var Regs K := ⟨Expression.const g * r.pc, r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.blake2s.code)
      #v[r.om0, r.om1, r.om2, r.om3, r.ocv, r.oout, r.omd]
    memRead (r.fp * r.om0) r.rm0 #v[r.m0[0], r.m0[1], 0]
    memRead (r.fp * r.om1) r.rm1 #v[r.m1[0], r.m1[1], 0]
    memRead (r.fp * r.om2) r.rm2 #v[r.m2[0], r.m2[1], 0]
    memRead (r.fp * r.om3) r.rm3 #v[r.m3[0], r.m3[1], 0]
    memRead (r.fp * r.ocv) r.rcv0 #v[r.cv0[0], r.cv0[1], 0]
    memRead (r.fp * (Expression.const g * r.ocv)) r.rcv1 #v[r.cv1[0], r.cv1[1], 0]
    memRead (r.fp * r.oout) r.rout0 #v[r.out0[0], r.out0[1], 0]
    memRead (r.fp * (Expression.const g * r.oout)) r.rout1 #v[r.out1[0], r.out1[1], 0]
    memRead (r.fp * r.omd) r.rmd #v[r.md[0], r.md[1], 0]
    pure next
  -- The push channels: their requirements are vacuous (Layer 5), the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Without core's `BitVec.reduceNeg` simproc, which misreads `-1 : K` (finding E6).
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The named assumption: Flock's proof of the compression relation on the row's limbs.
  Assumptions r _ := Blake2sRelation r
  -- The row is bound to the program and the image, and steps to the pushed successor.
  Spec := Blake2sSpec
  -- The local premise: the ten pull guarantees, the compression not among them.
  ProverAssumptions r data _ := Blake2sRowBindings r data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩ := h_holds
    obtain ⟨_, _, _, _, _, _, _, _, _, hvm0, hvm1, hvm2, hvm3, hvout0, hvout1, hvcv0, hvcv1, hvmd,
      _, _, _, _, _, _, _, _, _, _⟩ := h_input
    subst hvm0 hvm1 hvm2 hvm3 hvout0 hvout1 hvcv0 hvcv1 hvmd
    -- The pulled tuple is the entry of `BLAKE2S` with the row's operands (Layer 4).
    rw [blake2s_entry, decode_entry, Option.some.injEq] at hdec
    subst hdec
    refine (blake2s_spec_iff _ _ _).mpr
      ⟨⟨hfetch, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h_assumptions, rfl⟩
    · simpa only [E.ofCell, Vector.getElem_map] using hm0
    · simpa only [E.ofCell, Vector.getElem_map] using hm1
    · simpa only [E.ofCell, Vector.getElem_map] using hm2
    · simpa only [E.ofCell, Vector.getElem_map] using hm3
    · simpa only [E.ofCell, Vector.getElem_map] using hcv0
    · simpa only [E.ofCell, Vector.getElem_map] using hcv1
    · simpa only [E.ofCell, Vector.getElem_map] using hout0
    · simpa only [E.ofCell, Vector.getElem_map] using hout1
    · simpa only [E.ofCell, Vector.getElem_map] using hmd
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead, E.ofCell]
    -- The ten pull guarantees are the bindings; the tuple `main` emits is the fetched
    -- instruction's entry (Layer 4).
    obtain ⟨hfetch, hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩ := h_assumptions
    obtain ⟨_, _, _, _, _, _, _, _, _, hvm0, hvm1, hvm2, hvm3, hvout0, hvout1, hvcv0, hvcv1, hvmd,
      _, _, _, _, _, _, _, _, _, _⟩ := h_input
    subst hvm0 hvm1 hvm2 hvm3 hvout0 hvout1 hvcv0 hvcv1 hvmd
    simp only [E.ofCell, Vector.getElem_map] at hm0 hm1 hm2 hm3 hcv0 hcv1 hout0 hout1 hmd ⊢
    exact ⟨⟨_, hfetch, by rw [blake2s_entry, decode_entry]⟩, hm0, hm1, hm2, hm3, hcv0, hcv1,
      hout0, hout1, hmd⟩

/-- A bound row satisfies the constraints of `main` in the row environment over its data: local
completeness, which does not check the compression. The boundary with Flock, stated. -/
theorem blake2sRow_complete {r : Blake2sRow K} {data : ProverData K}
    (h : Blake2sRowBindings r data) :
    ConstraintsHold.Completeness (rowEnv data) ((blake2sTable.main (const r)).operations 0) :=
  (blake2sTable.completeness 0 (rowEnv data) (const r)
    -- No witness slot: the row environment uses the local witnesses vacuously.
    (by simp only [circuit_norm, blake2sTable, memRead, bytecodeRead, -BitVec.reduceNeg]) r
    ProvableType.eval_const_prover h).1

/-! ## Rows from steps -/

/-- The row of a step that fetches `BLAKE2S [o_{m₀}, …, o_{m₃}] o_cv o_out o_md` from
`(pc, fp)`: the registers, the operands, the nine cells read back from the image, and the
counts as parameters. Noncomputable: it reads the image. -/
noncomputable def blake2sRowOf (data : ProverData K) (pc fp om0 om1 om2 om3 ocv oout omd : K)
    (rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc : K) : Blake2sRow K :=
  ⟨pc, fp, om0, om1, om2, om3, ocv, oout, omd,
    (imageOf data).2.cellAt (fp * om0), (imageOf data).2.cellAt (fp * om1),
    (imageOf data).2.cellAt (fp * om2), (imageOf data).2.cellAt (fp * om3),
    (imageOf data).2.cellAt (fp * oout), (imageOf data).2.cellAt (fp * (g * oout)),
    (imageOf data).2.cellAt (fp * ocv), (imageOf data).2.cellAt (fp * (g * ocv)),
    (imageOf data).2.cellAt (fp * omd),
    rm0, rm1, rm2, rm3, rcv0, rcv1, rout0, rout1, rmd, rbc⟩

/-- A valid step that fetches `BLAKE2S` is represented by `blake2sRowOf`, with any counts:
`CompressCells` makes every cell canonical, so two limbs read it back. -/
theorem blake2sRowOf_spec {data : ProverData K} {pc fp om0 om1 om2 om3 ocv oout omd : K}
    {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.blake2s ![om0, om1, om2, om3] ocv oout omd))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next)
    (rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc : K) :
    Blake2sSpec (blake2sRowOf data pc fp om0 om1 om2 om3 ocv oout omd
      rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc) next data := by
  have h := hstep
  rw [step_of_fetch_eq_some hfetch] at h
  simp only [execute, Matrix.cons_val, Fin.isValue, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨m0, hm0, m1, hm1, m2, hm2, m3, hm3, cv0, hcv0, cv1, hcv1, out0, hout0, out1, hout1,
    md, hmd, u, hu, -⟩ := h
  obtain ⟨hcm, hccv0, hccv1, hcout0, hcout1, hcmd, -⟩ := guard_eq_some hu
  refine ⟨⟨hfetch, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hstep⟩
  · show (imageOf data).2.read (fp * om0) = some (E.ofCell ((imageOf data).2.cellAt (fp * om0)))
    rw [MemImage.ofCell_cellAt hm0 (hcm 0)]; exact hm0
  · show (imageOf data).2.read (fp * om1) = some (E.ofCell ((imageOf data).2.cellAt (fp * om1)))
    rw [MemImage.ofCell_cellAt hm1 (hcm 1)]; exact hm1
  · show (imageOf data).2.read (fp * om2) = some (E.ofCell ((imageOf data).2.cellAt (fp * om2)))
    rw [MemImage.ofCell_cellAt hm2 (hcm 2)]; exact hm2
  · show (imageOf data).2.read (fp * om3) = some (E.ofCell ((imageOf data).2.cellAt (fp * om3)))
    rw [MemImage.ofCell_cellAt hm3 (hcm 3)]; exact hm3
  · show (imageOf data).2.read (fp * ocv) = some (E.ofCell ((imageOf data).2.cellAt (fp * ocv)))
    rw [MemImage.ofCell_cellAt hcv0 hccv0]; exact hcv0
  · show (imageOf data).2.read (fp * (g * ocv)) =
      some (E.ofCell ((imageOf data).2.cellAt (fp * (g * ocv))))
    rw [MemImage.ofCell_cellAt hcv1 hccv1]; exact hcv1
  · show (imageOf data).2.read (fp * oout) = some (E.ofCell ((imageOf data).2.cellAt (fp * oout)))
    rw [MemImage.ofCell_cellAt hout0 hcout0]; exact hout0
  · show (imageOf data).2.read (fp * (g * oout)) =
      some (E.ofCell ((imageOf data).2.cellAt (fp * (g * oout))))
    rw [MemImage.ofCell_cellAt hout1 hcout1]; exact hout1
  · show (imageOf data).2.read (fp * omd) = some (E.ofCell ((imageOf data).2.cellAt (fp * omd)))
    rw [MemImage.ofCell_cellAt hmd hcmd]; exact hmd

/-- Every valid `BLAKE2S` step has a satisfying row, from the step alone: the compression a
valid step passes is what makes its nine cells canonical, hence readable back and bound. -/
theorem blake2s_step_complete {data : ProverData K} {pc fp om0 om1 om2 om3 ocv oout omd : K}
    {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.blake2s ![om0, om1, om2, om3] ocv oout omd))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next)
    (rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((blake2sTable.main (const (blake2sRowOf data pc fp om0 om1 om2 om3 ocv oout omd
        rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc))).operations 0) :=
  blake2sRow_complete
    (blake2sRowOf_spec hfetch hstep rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc).1

end LeanerVM.Arithmetization
