/-
  LeanerVM.Arithmetization.Tables.Jump

  The `JUMP` table: one Clean component per row, sound and complete for `step`.
  A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Channels
import Clean.Circuit.Formal
import Clean.Utils.Tactics.CircuitProofStart
import Mathlib.Algebra.CharP.Two

/-!
# The `JUMP` table

leanISA roadmap Layer 6 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `93c9d1ef`. Category B: the columns
are `crates/lean_vm/src/tables.rs:690-712` (`mod jump`, in that order), the two identities
`tables.rs:63-78` (`jump_identity`), the flushes `tables.rs:731-751` (`JumpTable::flushes`),
matching specification §7.5 (`doc/leanvm/body/07-instruction-tables.tex:94-112`).

**The row** `JumpRow` is the column list: `pc, fp`; the operands `o_c, o_d, o_f`; the condition
`v_cond`, the destination `v_pc` and the frame `v_fp`, each a single `K` limb; the memory counts
`r_c, r_d, r_f`; the bytecode count `r_bc`. The inverse `w` and the taken indicator `b` are
local witnesses of the component (`tables.rs:707-711`, "local witness columns"): the honest
prover sets `w = v_cond⁻¹` when `v_cond ≠ 0` and `0` otherwise, and `b = [v_cond ≠ 0]`.

**The constraints** are the two residuals `b + v_cond·w = 0` and `v_cond·(b + 1) = 0`. Together
they force `b = [v_cond ≠ 0]` (`flags_sound`): with `v_cond = 0` the first gives `b = 0`; with
`v_cond ≠ 0` the second gives `b = 1`. Booleanity of `b` alone would accept `b = 1` with
`v_cond = 0` and a wrong successor (roadmap acceptance test 8).

**The component** `jumpTable` pulls the state `(pc, fp)` and pushes the derived successor
`(b·v_pc + b·(g·pc) + g·pc, b·v_fp + b·fp + fp)`, in characteristic two the selection of
`(v_pc, v_fp)` when `b = 1` and of `(g·pc, fp)` when `b = 0`; reads the bytecode entry
`(JMP, o_c, o_d, o_f, 0, 0, 0, 0)` at `pc`; and reads the three cells `fp·o_c`, `fp·o_d`,
`fp·o_f` as single-limb words `(v, 0, 0)`. It returns the pushed successor, and `Spec` is
`step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next` (see
`LeanerVM.Arithmetization.Tables.Xor` for the template); the successor is a function of the
witness `b`, which is why the table returns it rather than naming it in `Spec` from the row.

## Wrong readings excluded

* The three memory reads carry literal zeros above the low limb, so the condition, destination
  and frame words are in `K` whether or not the branch is taken, as `step` asserts
  (acceptance test 7).
* `b·(b + 1) = 0` is not the constraint (acceptance test 8): `flags_sound` needs both
  residuals, and the mutated row `b = 1, v_cond = 0` of the tests fails the first.
* The successor is a degree-two coordinate of the state push, not a column: there is no
  `next_pc` column to constrain.
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

/-! ## The row -/

/-- The `JUMP` columns, in the order of `tables.rs:690-712`; the witnesses `w` and `b` are
local to the component. -/
structure JumpRow (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operand `o_c`, naming the condition cell. -/
  oc : F
  /-- The operand `o_d`, naming the destination cell. -/
  od : F
  /-- The operand `o_f`, naming the frame cell. -/
  of : F
  /-- The condition `v_cond`, the low limb of the word at `fp · o_c`. -/
  vcond : F
  /-- The destination `v_pc`, the low limb of the word at `fp · o_d`. -/
  vpc : F
  /-- The frame `v_fp`, the low limb of the word at `fp · o_f`. -/
  vfp : F
  /-- The read count of the condition cell. -/
  rc : F
  /-- The read count of the destination cell. -/
  rd : F
  /-- The read count of the frame cell. -/
  rf : F
  /-- The read count of the bytecode entry at `pc`. -/
  rbc : F
  deriving ProvableStruct

/-! ## Load-bearing lemmas -/

/-- The two residuals force the indicator: `b = [c ≠ 0]` (specification §7.5; roadmap
acceptance test 8). -/
theorem flags_sound {c w b : K} (h1 : b + c * w = 0) (h2 : c * (b + 1) = 0) :
    b = if c = 0 then 0 else 1 := by
  split_ifs with hc
  · subst hc
    rwa [zero_mul, add_zero] at h1
  · exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hc)

/-- The honest witnesses satisfy the two residuals: `w = c⁻¹` (or `0`) and `b = [c ≠ 0]`. -/
theorem flags_complete (c : K) :
    (if c = 0 then 0 else 1) + c * (if c = 0 then 0 else c⁻¹) = 0 ∧
      c * ((if c = 0 then 0 else 1) + 1) = 0 := by
  split_ifs with hc
  · subst hc
    exact ⟨by rw [zero_mul, add_zero], by rw [zero_mul]⟩
  · exact ⟨by rw [mul_inv_cancel₀ hc, CharTwo.add_self_eq_zero],
      by rw [CharTwo.add_self_eq_zero, mul_zero]⟩

/-- Limb `i` of the zero word is zero. -/
theorem limb_zero (i : Fin 3) : (0 : E).limb i = 0 :=
  CompPoly.Extension.Ext.coeff_zero (P := BF64.ext3Params) i

/-- A single-limb word is zero exactly when its limb is. -/
theorem ofLimbs_eq_zero_iff (c : K) : E.ofLimbs c 0 0 = 0 ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg (fun z : E ↦ z.limb 0) h
    simpa only [limb_ofLimbs, limb_zero, Matrix.cons_val_zero] using this
  · rintro rfl
    exact E.ext fun i ↦ by rw [limb_zero]; fin_cases i <;> simp

/-- A word with zero upper limbs lies in `K`. -/
theorem isInK_ofLimbs' (c : K) : IsInK (E.ofLimbs c 0 0) := ⟨by simp, by simp⟩

/-- The bytecode tuple of a `JUMP` row is the entry of the instruction it names (Layer 4). -/
theorem jump_entry (oc od of : K) :
    #v[Opcode.jump.code] ++ #v[oc, od, of, 0, 0, 0, 0] = entry (.jump oc od of) := rfl

/-! ## The table -/

/-- The `JUMP` table (specification §7.5; `tables.rs:690-820`): the witnesses `w`, `b`, the two
residual constraints, the state pull and the push of the derived successor, the bytecode read
of `(JMP, o_c, o_d, o_f, 0, 0, 0, 0)`, and the three single-limb reads. Returns the pushed
successor. -/
def jumpTable : GeneralFormalCircuit K JumpRow Regs where
  main r := do
    -- The honest inverse `w = v_cond⁻¹` (`0` when `v_cond = 0`) and the indicator `b`.
    let w ← witness (.ite (r.vcond =? 0) 0 r.vcond⁻¹)
    let b ← witness (.ite (r.vcond =? 0) 0 1)
    assertZero (b + r.vcond * w)
    assertZero (r.vcond * (b + 1))
    let next : Var Regs K :=
      ⟨b * r.vpc + b * (Expression.const g * r.pc) + Expression.const g * r.pc,
        b * r.vfp + b * r.fp + r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.jump.code) #v[r.oc, r.od, r.of, 0, 0, 0, 0]
    memRead (r.fp * r.oc) r.rc #v[r.vcond, 0, 0]
    memRead (r.fp * r.od) r.rd #v[r.vpc, 0, 0]
    memRead (r.fp * r.of) r.rf #v[r.vfp, 0, 0]
    pure next
  -- The push channels: their requirements are vacuous (Layer 5), the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Without core's `BitVec.reduceNeg` simproc, which misreads `-1 : K` (finding E6).
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The row is a step: from its registers the machine steps to the pushed successor.
  Spec r next data := step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next
  -- The honest row: the operands are the fetched instruction's and the three cells hold the
  -- `K` words `v_cond`, `v_pc`, `v_fp`.
  ProverAssumptions r data _ :=
    (programOf data).fetch r.pc = some (.jump r.oc r.od r.of) ∧
    (imageOf data).2.read (r.fp * r.oc) = some (E.ofLimbs r.vcond 0 0) ∧
    (imageOf data).2.read (r.fp * r.od) = some (E.ofLimbs r.vpc 0 0) ∧
    (imageOf data).2.read (r.fp * r.of) = some (E.ofLimbs r.vfp 0 0)
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨hw, hb, ⟨ins, hfetch, hdec⟩, hc, hd, hf⟩ := h_holds
    rw [jump_entry, decode_entry, Option.some.injEq] at hdec
    subst hdec
    have hind := flags_sound hw hb
    rw [step_of_fetch_eq_some hfetch]
    simp only [execute, guard, hc, hd, hf, isInK_ofLimbs', and_self, ite_true, Option.bind_some,
      Option.bind_eq_bind, Option.pure_def, ofLimbs_eq_zero_iff, limb_ofLimbs, Matrix.cons_val_zero,
      Regs.next]
    split_ifs at hind ⊢ with hc0
    · -- Not taken: `b = 0`, the successor is `(g·pc, fp)`.
      simp only [hind, zero_mul, zero_add]
    · -- Taken: `b = 1`, the successor is `(v_pc, v_fp)` since `x + x = 0`.
      simp only [hind, one_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨hfetch, hc, hd, hf⟩ := h_assumptions
    obtain ⟨hw, hb⟩ := h_env
    rw [hw, hb]
    exact ⟨(flags_complete _).1, (flags_complete _).2,
      ⟨_, hfetch, by rw [jump_entry, decode_entry]⟩, hc, hd, hf⟩

end LeanerVM.Arithmetization
