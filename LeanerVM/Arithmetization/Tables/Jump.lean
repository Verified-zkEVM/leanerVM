/-
  LeanerVM.Arithmetization.Tables.Jump

  The `JUMP` table: one Clean component per row, sound and complete for the row's functional
  specification, its bindings to the program and the image together with Layer 3's `step`.
  A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Tables.Basic
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

**The contract.** `JumpRowBindings r data` binds the row to the program and the image: the
instruction at `pc` is `JUMP o_c o_d o_f`, and the three cells hold the `K` words `v_cond`,
`v_pc`, `v_fp`, taken or not. `JumpSpec r next data` is the bindings and the step;
`jump_spec_iff` expands it: the successor is `(v_pc, v_fp)` when `v_cond ≠ 0` and `(g·pc, fp)`
otherwise; `jump_spec_step` projects the step. The bindings alone make a successor exist
(`jump_bindings_iff`), so they are also the local completeness premise. The specification does
not mention `w`: with `v_cond = 0` the residuals accept every `w`, and the honest generator's
`0` is one satisfying assignment among all of them.

**The component** `jumpTable` pulls the state `(pc, fp)` and pushes the derived successor
`(b·v_pc + b·(g·pc) + g·pc, b·v_fp + b·fp + fp)` (`jump_output`), in characteristic two the
selection of `(v_pc, v_fp)` when `b = 1` and of `(g·pc, fp)` when `b = 0`; reads the bytecode
entry `(JMP, o_c, o_d, o_f, 0, 0, 0, 0)` at `pc`; and reads the three cells `fp·o_c`, `fp·o_d`,
`fp·o_f` as single-limb words `(v, 0, 0)`. It returns the pushed successor, and `Spec` is
`JumpSpec`: the successor is a function of the witness `b`, which is why the table returns it
rather than naming it in `Spec` from the row; `ProverAssumptions r data _ :=
∃ next, JumpSpec r next data`.

**The witness discipline.** `jump_env_iff` says exactly which prover environments use the two
local witnesses: slot `offset` is the honest inverse and slot `offset + 1` the honest
indicator of the row's condition. `jumpEnv data r` is that environment for a row over its
data, and `jumpRow_complete` pushes any row with the semantic premise through `completeness`
in it. Clean's array generator `Circuit.witgen` computes the same two values (the tests run
it), but its environment carries no data, so the data-carrying environment is `jumpEnv`, whose
witness discipline is the theorem.

**Rows from steps.** `jumpRowOf data pc fp o_c o_d o_f r_c r_d r_f r_bc` reads the three low
limbs back from the image; `jumpRowOf_spec`, `jump_row_exists`, `jump_bindings_of_constraints`
and `jump_residuals_of_constraints` (the two residuals, read off the constraints `main` emits)
are the `XOR` statements for this table.

## Wrong readings excluded

* The three memory reads carry literal zeros above the low limb, so the condition, destination
  and frame words are in `K` whether or not the branch is taken, as `step` asserts
  (acceptance test 7).
* `b·(b + 1) = 0` is not the constraint (acceptance test 8): `flags_sound` needs both
  residuals, and the mutated row `b = 1, v_cond = 0` of the tests fails the first
  (`jump_residuals_of_constraints`).
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

/-- The bytecode tuple of a `JUMP` row is the entry of the instruction it names (Layer 4). -/
theorem jump_entry (oc od of : K) :
    #v[Opcode.jump.code] ++ #v[oc, od, of, 0, 0, 0, 0] = entry (.jump oc od of) := rfl

/-! ## The contract -/

/-- The row's bindings to the program and the image: the instruction at `pc` is
`JUMP o_c o_d o_f`, and the three cells hold the row's `K` words. -/
def JumpRowBindings (r : JumpRow K) (data : ProverData K) : Prop :=
  (programOf data).fetch r.pc = some (.jump r.oc r.od r.of) ∧
  (imageOf data).2.read (r.fp * r.oc) = some (E.ofLimbs r.vcond 0 0) ∧
  (imageOf data).2.read (r.fp * r.od) = some (E.ofLimbs r.vpc 0 0) ∧
  (imageOf data).2.read (r.fp * r.of) = some (E.ofLimbs r.vfp 0 0)

/-- The functional specification of a `JUMP` row: it is bound to the program and the image,
and from its registers the machine steps to `next`. -/
def JumpSpec (r : JumpRow K) (next : Regs K) (data : ProverData K) : Prop :=
  JumpRowBindings r data ∧ step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next

/-- `JumpSpec`, expanded: the bindings, and the successor is `(v_pc, v_fp)` when the condition
is nonzero and the fall-through `(g·pc, fp)` otherwise. -/
theorem jump_spec_iff (r : JumpRow K) (next : Regs K) (data : ProverData K) :
    JumpSpec r next data ↔
      JumpRowBindings r data ∧
        next = if r.vcond = 0 then Regs.next ⟨r.pc, r.fp⟩ else ⟨r.vpc, r.vfp⟩ := by
  unfold JumpSpec
  constructor
  · rintro ⟨⟨hfetch, hc, hd, hf⟩, hstep⟩
    refine ⟨⟨hfetch, hc, hd, hf⟩, ?_⟩
    rw [step_of_fetch_eq_some hfetch] at hstep
    simp only [execute, hc, hd, hf, Option.bind_eq_bind, Option.bind_some,
      guard_bind_eq_some_iff, isInK_ofLimbs, and_self, true_and, Option.pure_def,
      Option.some.injEq, ofLimbs_eq_zero_iff, limb_ofLimbs, Matrix.cons_val_zero] at hstep
    exact hstep.symm
  · rintro ⟨⟨hfetch, hc, hd, hf⟩, rfl⟩
    refine ⟨⟨hfetch, hc, hd, hf⟩, ?_⟩
    rw [step_of_fetch_eq_some hfetch]
    simp only [execute, hc, hd, hf, Option.bind_eq_bind, Option.bind_some,
      guard_bind_eq_some_iff, isInK_ofLimbs, and_self, Option.pure_def, ofLimbs_eq_zero_iff,
      limb_ofLimbs, Matrix.cons_val_zero]

/-- The step, projected out of the specification. -/
theorem jump_spec_step {r : JumpRow K} {next : Regs K} {data : ProverData K}
    (h : JumpSpec r next data) : step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next :=
  h.2

/-- The bindings alone make the row step: they are the local completeness premise. -/
theorem jump_bindings_iff (r : JumpRow K) (data : ProverData K) :
    JumpRowBindings r data ↔ ∃ next, JumpSpec r next data := by
  constructor
  · intro h
    exact ⟨_, (jump_spec_iff _ _ _).mpr ⟨h, rfl⟩⟩
  · rintro ⟨next, h⟩
    exact h.1

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
  -- The row is bound to the program and the image, and steps to the pushed successor.
  Spec := JumpSpec
  -- The semantic premise: the row is bound and steps somewhere (the bindings, by
  -- `jump_bindings_iff`).
  ProverAssumptions r data _ := ∃ next, JumpSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨hw, hb, ⟨ins, hfetch, hdec⟩, hc, hd, hf⟩ := h_holds
    rw [jump_entry, decode_entry, Option.some.injEq] at hdec
    subst hdec
    have hind := flags_sound hw hb
    refine (jump_spec_iff _ _ _).mpr ⟨⟨hfetch, hc, hd, hf⟩, ?_⟩
    split_ifs at hind ⊢ with hc0
    · -- Not taken: `b = 0`, the successor is `(g·pc, fp)`.
      simp only [hind, zero_mul, zero_add, Regs.next]
    · -- Taken: `b = 1`, the successor is `(v_pc, v_fp)` since `x + x = 0`.
      simp only [hind, one_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨hfetch, hc, hd, hf⟩ := (jump_bindings_iff _ _).mpr h_assumptions
    obtain ⟨hw, hb⟩ := h_env
    rw [hw, hb]
    exact ⟨(flags_complete _).1, (flags_complete _).2,
      ⟨_, hfetch, by rw [jump_entry, decode_entry]⟩, hc, hd, hf⟩

/-- The returned successor: the derived `(b·v_pc + b·(g·pc) + g·pc, b·v_fp + b·fp + fp)` with
`b` the witness in slot `offset + 1`, for every environment. -/
theorem jump_output (env : Environment K) (offset : ℕ) (r : Var JumpRow K) :
    eval env ((jumpTable.main r).output offset) =
      ⟨env.get (offset + 1) * (eval env r).vpc + env.get (offset + 1) * (g * (eval env r).pc) +
          g * (eval env r).pc,
        env.get (offset + 1) * (eval env r).vfp + env.get (offset + 1) * (eval env r).fp +
          (eval env r).fp⟩ := by
  simp only [circuit_norm, jumpTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The constraints `main` emits on a row include its four pull guarantees. -/
theorem jump_bindings_of_constraints {env : Environment K} {r : Var JumpRow K} {offset : ℕ}
    (h : ConstraintsHold.Soundness env ((jumpTable.main r).operations offset)) :
    JumpRowBindings (eval env r) env.data :=
  (jumpTable.soundness offset env r (eval env r) rfl trivial h).1.1

/-- The constraints `main` emits on a row include the two residuals on the witnesses in slots
`offset` (the inverse) and `offset + 1` (the indicator). -/
theorem jump_residuals_of_constraints {env : Environment K} {r : Var JumpRow K} {offset : ℕ}
    (h : ConstraintsHold.Soundness env ((jumpTable.main r).operations offset)) :
    env.get (offset + 1) + (eval env r).vcond * env.get offset = 0 ∧
      (eval env r).vcond * (env.get (offset + 1) + 1) = 0 := by
  -- As `circuit_proof_start` does: the row destructured into its columns, the table unfolded
  -- by `dsimp` (unfolding it by `simp` exhausts the recursion depth), then `circuit_norm`.
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := r
  dsimp only [jumpTable] at h
  simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg] at h ⊢
  exact ⟨h.1, h.2.1⟩

/-! ## The witness discipline -/

/-- A witness program's conditional on a decided field equality is the conditional on the
equality of the evaluations. Applied before `circuit_norm` descends into the `decide` (the `↓`
below): rewriting underneath a `decide` leaves its `Decidable` instance behind, an ill-typed
term no later rewrite can touch (status finding E7). -/
private theorem ite_feq {α : Type} (ctx : Witgen.Ctx K) (x y : Witgen.FExpr K) (a b : α) :
    (if (Witgen.BExpr.feq x y).eval ctx = true then a else b) =
      if x.eval ctx = y.eval ctx then a else b := by
  simp only [Witgen.BExpr.eval_feq_iff]

/-- A prover environment uses the two local witnesses of a `JUMP` row exactly when slot
`offset` is the honest inverse and slot `offset + 1` the honest indicator of the condition. -/
theorem jump_env_iff (env : ProverEnvironment K) (offset : ℕ) (r : Var JumpRow K) :
    env.UsesLocalWitnessesCompleteness offset ((jumpTable.main r).operations offset) ↔
      env.get offset = (if (eval env r).vcond = 0 then 0 else (eval env r).vcond⁻¹) ∧
        env.get (offset + 1) = (if (eval env r).vcond = 0 then 0 else 1) := by
  -- As `circuit_proof_start` does: the row destructured into its columns, the table unfolded
  -- by `dsimp`, then `circuit_norm`, with `ite_feq` reading the witness programs' `Bool`
  -- conditions back as propositions before the descent (E7).
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := r
  dsimp only [jumpTable]
  simp only [↓ite_feq, circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
  -- The two sides differ only in the instance paths of `K`'s field structure.
  exact Iff.rfl

/-- The honest prover environment of a `JUMP` row over `data`: slot `0` the inverse `w`, slot
`1` the indicator `b`, as the two witness programs compute them; the data; no hints. -/
def jumpEnv (data : ProverData K) (r : JumpRow K) : ProverEnvironment K :=
  ⟨⟨fun j ↦ if j = 0 then (if r.vcond = 0 then 0 else r.vcond⁻¹)
      else if j = 1 then (if r.vcond = 0 then 0 else 1) else 0, data⟩, default⟩

/-- `jumpEnv` uses the row's local witnesses. -/
theorem jumpEnv_usesLocalWitnesses (data : ProverData K) (r : JumpRow K) :
    (jumpEnv data r).UsesLocalWitnessesCompleteness 0
      ((jumpTable.main (const r)).operations 0) := by
  rw [jump_env_iff, ProvableType.eval_const_prover]
  exact ⟨rfl, rfl⟩

/-- A row with the semantic premise satisfies the constraints of `main` in its honest
environment over its data: local completeness, literally, witnesses included. -/
theorem jumpRow_complete {r : JumpRow K} {data : ProverData K}
    (h : ∃ next, JumpSpec r next data) :
    ConstraintsHold.Completeness (jumpEnv data r) ((jumpTable.main (const r)).operations 0) :=
  (jumpTable.completeness 0 (jumpEnv data r) (const r) (jumpEnv_usesLocalWitnesses data r) r
    ProvableType.eval_const_prover h).1

/-! ## Rows from steps -/

/-- The row of a step that fetches `JUMP o_c o_d o_f` from `(pc, fp)`: the registers, the
operands, the three low limbs read back from the image, and the counts as parameters.
Noncomputable: it reads the image. -/
noncomputable def jumpRowOf (data : ProverData K) (pc fp oc od of rc rd rf rbc : K) :
    JumpRow K :=
  ⟨pc, fp, oc, od, of, (limbsAt (imageOf data).2 (fp * oc))[0],
    (limbsAt (imageOf data).2 (fp * od))[0], (limbsAt (imageOf data).2 (fp * of))[0],
    rc, rd, rf, rbc⟩

/-- A valid step that fetches `JUMP o_c o_d o_f` is represented by `jumpRowOf`, with any
counts. -/
theorem jumpRowOf_spec {data : ProverData K} {pc fp oc od of : K} {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.jump oc od of))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (rc rd rf rbc : K) :
    JumpSpec (jumpRowOf data pc fp oc od of rc rd rf rbc) next data := by
  have h := hstep
  rw [step_of_fetch_eq_some hfetch] at h
  simp only [execute, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, d, hd, f, hf, u, hu, -⟩ := h
  obtain ⟨hcK, hdK, hfK⟩ := guard_eq_some hu
  refine ⟨⟨hfetch, ?_, ?_, ?_⟩, hstep⟩
  · show (imageOf data).2.read (fp * oc) =
      some (E.ofLimbs (limbsAt (imageOf data).2 (fp * oc))[0] 0 0)
    rw [limbsAt_getElem_zero hc, ofLimbs_of_isInK hcK]; exact hc
  · show (imageOf data).2.read (fp * od) =
      some (E.ofLimbs (limbsAt (imageOf data).2 (fp * od))[0] 0 0)
    rw [limbsAt_getElem_zero hd, ofLimbs_of_isInK hdK]; exact hd
  · show (imageOf data).2.read (fp * of) =
      some (E.ofLimbs (limbsAt (imageOf data).2 (fp * of))[0] 0 0)
    rw [limbsAt_getElem_zero hf, ofLimbs_of_isInK hfK]; exact hf

/-- A valid step that fetches `JUMP o_c o_d o_f` admits a row with the same registers and
operands and any counts. -/
theorem jump_row_exists {data : ProverData K} {pc fp oc od of : K} {next : Regs K}
    (hfetch : (programOf data).fetch pc = some (.jump oc od of))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (rc rd rf rbc : K) :
    ∃ c d f, JumpSpec ⟨pc, fp, oc, od, of, c, d, f, rc, rd, rf, rbc⟩ next data :=
  ⟨_, _, _, jumpRowOf_spec hfetch hstep rc rd rf rbc⟩

end LeanerVM.Arithmetization
