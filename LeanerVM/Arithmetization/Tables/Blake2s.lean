/-
  LeanerVM.Arithmetization.Tables.Blake2s

  The `BLAKE2S` table: one Clean component per row, sound and complete for `step` under the
  named assumption that Flock proves the compression relation on the row's eighteen limbs.
  A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Channels
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

**The component** `blake2sTable` pulls the state `(pc, fp)` and pushes `(g·pc, fp)`, reads the
bytecode entry `(B2S, o_{m₀}, o_{m₁}, o_{m₂}, o_{m₃}, o_cv, o_out, o_md)` at `pc`, and reads
the nine cells in the order of §7.6: the four message cells at `fp·o_{mᵢ}`, the chaining-value
pair at `fp·o_cv` and `fp·(g·o_cv)`, the output pair at `fp·o_out` and `fp·(g·o_out)`, and the
metadata cell at `fp·o_md`, each as `(lo, hi, 0)`. It returns the pushed successor, and `Spec`
is `step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next` (see
`LeanerVM.Arithmetization.Tables.Xor` for the template).

**The assumption.** Flock (issue #3) proves, for every row, the compression relation on the
row's eighteen limbs; this table consumes that proof as its `Assumptions` field
`Blake2sRelation r`, Layer 1's `CompressCells` on the nine canonical cells the limbs form. It
is the one named hypothesis of the layer: every consumer of this table carries it until the
Flock roadmap supplies the circuit, and nothing here re-proves or re-states the compression.

## Wrong readings excluded

* All nine cells are canonical, the two output cells included (roadmap acceptance test 12):
  every memory read carries a literal zero top limb, so an image word with a nonzero top limb
  cannot balance the bus (the mutated row in the tests).
* The second cell of each pair is at `g·fp·o`, a free `×g` on the product coordinate
  (`Prod(FP, O_CV, 1)`), matching `execute`'s `fp · (g · o_cv)`.
* The two finalization flags are the two words of the metadata cell's limb `1`, entering
  `compress` unchanged (Layer 1, acceptance test 10); the table constrains nothing about them.
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

/-- The canonical word of a cell's two limbs. -/
def cellOf (v : Vector K 2) : E := E.ofLimbs v[0] v[1] 0

/-- The compression relation on a row's eighteen limbs, as Flock proves it (issue #3):
Layer 1's `CompressCells` on the nine canonical cells. The named assumption of the table. -/
def Blake2sRelation (r : Blake2sRow K) : Prop :=
  CompressCells ![cellOf r.m0, cellOf r.m1, cellOf r.m2, cellOf r.m3] (cellOf r.cv0)
    (cellOf r.cv1) (cellOf r.out0) (cellOf r.out1) (cellOf r.md)

/-! ## Load-bearing lemmas -/

/-- The bytecode tuple of a `BLAKE2S` row is the entry of the instruction it names (Layer 4). -/
theorem blake2s_entry (om0 om1 om2 om3 ocv oout omd : K) :
    #v[Opcode.blake2s.code] ++ #v[om0, om1, om2, om3, ocv, oout, omd] =
      entry (.blake2s ![om0, om1, om2, om3] ocv oout omd) := rfl

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
  -- The row is a step: from its registers the machine steps to the pushed successor.
  Spec r next data := step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next
  -- The honest row: the operands are the fetched instruction's and the nine cells hold the
  -- image's canonical words.
  ProverAssumptions r data _ :=
    (programOf data).fetch r.pc = some (.blake2s ![r.om0, r.om1, r.om2, r.om3] r.ocv r.oout r.omd) ∧
    (imageOf data).2.read (r.fp * r.om0) = some (cellOf r.m0) ∧
    (imageOf data).2.read (r.fp * r.om1) = some (cellOf r.m1) ∧
    (imageOf data).2.read (r.fp * r.om2) = some (cellOf r.m2) ∧
    (imageOf data).2.read (r.fp * r.om3) = some (cellOf r.m3) ∧
    (imageOf data).2.read (r.fp * r.ocv) = some (cellOf r.cv0) ∧
    (imageOf data).2.read (r.fp * (g * r.ocv)) = some (cellOf r.cv1) ∧
    (imageOf data).2.read (r.fp * r.oout) = some (cellOf r.out0) ∧
    (imageOf data).2.read (r.fp * (g * r.oout)) = some (cellOf r.out1) ∧
    (imageOf data).2.read (r.fp * r.omd) = some (cellOf r.md)
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead, Blake2sRelation, cellOf]
    obtain ⟨⟨ins, hfetch, hdec⟩, hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩ := h_holds
    obtain ⟨_, _, _, _, _, _, _, _, _, hvm0, hvm1, hvm2, hvm3, hvout0, hvout1, hvcv0, hvcv1, hvmd,
      _, _, _, _, _, _, _, _, _, _⟩ := h_input
    subst hvm0 hvm1 hvm2 hvm3 hvout0 hvout1 hvcv0 hvcv1 hvmd
    rw [blake2s_entry, decode_entry, Option.some.injEq] at hdec
    subst hdec
    simp only [Vector.getElem_map] at h_assumptions
    rw [step_of_fetch_eq_some hfetch]
    simp only [execute, guard, hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd, h_assumptions,
      Matrix.cons_val, Fin.isValue, ite_true, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Regs.next]
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead, cellOf]
    obtain ⟨hfetch, hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩ := h_assumptions
    obtain ⟨_, _, _, _, _, _, _, _, _, hvm0, hvm1, hvm2, hvm3, hvout0, hvout1, hvcv0, hvcv1, hvmd,
      _, _, _, _, _, _, _, _, _, _⟩ := h_input
    subst hvm0 hvm1 hvm2 hvm3 hvout0 hvout1 hvcv0 hvcv1 hvmd
    simp only [Vector.getElem_map] at hm0 hm1 hm2 hm3 hcv0 hcv1 hout0 hout1 hmd ⊢
    exact ⟨⟨_, hfetch, by rw [blake2s_entry, decode_entry]⟩, hm0, hm1, hm2, hm3, hcv0, hcv1,
      hout0, hout1, hmd⟩

end LeanerVM.Arithmetization
