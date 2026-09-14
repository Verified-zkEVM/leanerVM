/-
  LeanerVM.Arithmetization.Tables.Deref

  The `DEREF` table: one Clean component per row, sound and complete for the relation the row
  refines, its bindings to a program and an image together with Layer 3's `step`.
  A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Tables.Basic
import Clean.Circuit.Formal
import Clean.Utils.Tactics.CircuitProofStart
import Mathlib.Algebra.CharP.Two

/-!
# The `DEREF` table

leanISA roadmap Layer 6 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `93c9d1ef`. Category B: the columns
are `crates/lean_vm/src/tables.rs:590-613` (`mod deref`, in that order), the store coordinates
`tables.rs:615-627` (`deref_store`), the flushes `tables.rs:637-650` (`DerefTable::flushes`),
matching specification §7.4 (`doc/leanvm/body/07-instruction-tables.tex:66-92`). There is no
constraint; the flags are not constrained Boolean, since the public program's decoder admits
only the three pairs (Layer 4; roadmap acceptance test 18).

**The row** `DerefRow` is the column list: `pc, fp`; the operands `o₁, o₂, o₃`; the flags
`f_pc, f_fp`; the pointer `p`, a single `K` limb; the local word `v₃` as three limbs; the memory
counts `r₁, r₂, r₃`; the bytecode count `r_bc`. The target word is never a column: its limbs
ride the target read as `(f̄·v₃₀ + f_pc·(g²·pc) + f_fp·fp, f̄·v₃₁, f̄·v₃₂)` with
`f̄ = 1 + f_pc + f_fp`, the flag-selected source of §7.4, which `storeCoords_eval` identifies
with Layer 3's `derefSource` at each of the three flag settings.

**The relation.** `DerefBindings prog mem r mode` binds the row to a program and an image for
a store mode: the instruction at `pc` is `DEREF o₁ o₂ o₃ mode` (`fetch_eq`), the row's flags
are the mode's (`flags_eq`, `derefFlags`), the pointer cell `fp·o₁` holds `p` in `K`
(`ptr_eq`), and the local cell `fp·o₃` holds the row's word (`local_eq`). `DerefRefines prog
mem r next` is the bindings for some mode and the step (`step_eq`); `deref_refines_iff` expands
it, with the same mode: the target cell `p·o₂` holds `derefSource mode (pc, fp)` of the local
word, the return address `g²·pc`, or `fp`, and the successor is `(g·pc, fp)`. The local cell
is read in every mode. `DerefSpec r next data` adapts the relation to Clean's prover data and
is the table's `Spec`; `ProverAssumptions r data _ := ∃ next, DerefSpec r next data` is the
honest prover's row (see `LeanerVM.Arithmetization.Tables.Xor` for the template), proved of
the row of any valid step by `derefRowOf_refines`.

**The component** `derefTable` pulls the state `(pc, fp)`, pushes and returns `(g·pc, fp)`,
reads the bytecode entry `(DRF, o₁, o₂, o₃, f_pc, f_fp, 0, 0)` at `pc`, reads the pointer cell
`fp·o₁` as `(p, 0, 0)`, the local cell `fp·o₃`, and the target cell `p·o₂`, in the order of
§7.4; `Spec` is `DerefSpec`. Soundness reads the fetched instruction off the bytecode pull
through Layer 4's `decode_deref_eq_some_iff`: the pulled tuple *is* an instruction, so its
flag pair is a store mode's (a pair that is no mode's decodes to nothing, and such a row cannot
pull its entry), and the target read's coordinates are that mode's source (`storeCoords_eval`).
Completeness discharges the four pulls from the semantic premise through `deref_refines_iff`:
the tuple `main` emits decodes to the fetched instruction (Layer 4's `decode_entry`), and the
target coordinates it emits are the mode's source.

**Rows from steps.** `derefRowOf mem pc fp o₁ o₂ o₃ mode r₁ r₂ r₃ rbc` is the row of a step
that fetches `DEREF o₁ o₂ o₃ mode` over the image `mem`: the mode's flags, the pointer's low
limb and the local word read back from the image (`MemImage.limbsAt`); `derefRowOf_refines`
proves it refines the relation, and `deref_step_complete` its acceptance by `main` over the
prover data, from the step alone.

## Wrong readings excluded

* The pointer read carries literal zeros above its low limb (`memory_k`, `tables.rs:172-174`),
  so a pointer word outside `K` cannot balance the bus; `step` asserts `IsInK p` the same way.
* The local cell is read in every mode, `pc` and `fp` modes included (acceptance test 6):
  `memRead (fp·o₃)` is unconditional, as is the third read of `execute`, and `DerefBindings`
  binds it in every mode.
* The return address is `g²·pc`, a free `×g²` on the product coordinate (`Prod(FPC, PC, 2)`),
  never `pc + 2`.
* `DerefRefines` names the mode: the flag pair `(1, 1)` is no `derefFlags mode`, so a row
  carrying it fails its bindings at every counter, where the old step-only reading accepted it
  (the review's counterexample, in the tests).
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

/-! ## The row -/

/-- The `DEREF` columns, in the order of `tables.rs:590-613`. -/
structure DerefRow (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operand `o₁`, naming the pointer cell. -/
  o1 : F
  /-- The operand `o₂`, the pointer-relative offset of the target. -/
  o2 : F
  /-- The operand `o₃`, naming the local cell. -/
  o3 : F
  /-- The flag `f_pc`. -/
  fpc : F
  /-- The flag `f_fp`. -/
  ffp : F
  /-- The pointer `p`, the low limb of the word at `fp · o₁`. -/
  p : F
  /-- The local word at `fp · o₃`, as limbs. -/
  v3 : Vector F 3
  /-- The read count of the pointer cell. -/
  r1 : F
  /-- The read count of the target cell. -/
  r2 : F
  /-- The read count of the local cell. -/
  r3 : F
  /-- The read count of the bytecode entry at `pc`. -/
  rbc : F
  deriving ProvableStruct

/-! ## The store coordinates -/

/-- The store coordinates evaluate to Layer 3's `derefSource` at each flag setting
(specification §7.4; `tables.rs:615-627`): the local word in `cell` mode, `g²·pc` in `pc` mode,
`fp` in `fp` mode. -/
theorem storeCoords_eval (mode : DerefMode) (pc fp v30 v31 v32 : K) :
    E.ofLimbs
        ((1 + (derefFlags mode).1 + (derefFlags mode).2) * v30 +
          (derefFlags mode).1 * (g ^ 2 * pc) + (derefFlags mode).2 * fp)
        ((1 + (derefFlags mode).1 + (derefFlags mode).2) * v31)
        ((1 + (derefFlags mode).1 + (derefFlags mode).2) * v32) =
      derefSource mode ⟨pc, fp⟩ (E.ofLimbs v30 v31 v32) := by
  cases mode <;>
    simp only [derefFlags, derefSource, ofK_eq_ofLimbs, add_zero, zero_add, one_mul, zero_mul,
      CharTwo.add_self_eq_zero]

/-! ## The relation -/

/-- The row's bindings to a program and an image for a store mode: the instruction at `pc` is
`DEREF o₁ o₂ o₃ mode`, the flags are the mode's, the pointer cell holds `p` in `K`, and the
local cell holds the row's word. -/
structure DerefBindings {κ : ℕ} (prog : Program) (mem : MemImage κ) (r : DerefRow K)
    (mode : DerefMode) : Prop where
  /-- The instruction at `pc` is `DEREF o₁ o₂ o₃ mode`. -/
  fetch_eq : prog.fetch r.pc = some (.deref r.o1 r.o2 r.o3 mode)
  /-- The row's flags are the mode's. -/
  flags_eq : derefFlags mode = (r.fpc, r.ffp)
  /-- The pointer cell `fp · o₁` holds `p`, a word in `K`. -/
  ptr_eq : mem.read (r.fp * r.o1) = some (E.ofLimbs r.p 0 0)
  /-- The local cell `fp · o₃` holds the row's word `v₃`. -/
  local_eq : mem.read (r.fp * r.o3) = some (E.ofLimbs r.v3[0] r.v3[1] r.v3[2])

/-- The relation a `DEREF` row refines: it is bound to the program and the image for some store
mode, and from its registers the machine steps to `next`. -/
structure DerefRefines {κ : ℕ} (prog : Program) (mem : MemImage κ) (r : DerefRow K)
    (next : Regs K) : Prop where
  /-- The row is bound to the program and the image, for some store mode. -/
  bindings : ∃ mode, DerefBindings prog mem r mode
  /-- From the row's registers the machine steps to `next`. -/
  step_eq : step prog mem ⟨r.pc, r.fp⟩ = some next

/-- `DerefRefines`, expanded with the same mode: the bindings, the target cell `p·o₂` holds the
source the mode selects, and the successor is the fall-through `(g·pc, fp)`. -/
theorem deref_refines_iff {κ : ℕ} (prog : Program) (mem : MemImage κ) (r : DerefRow K)
    (next : Regs K) :
    DerefRefines prog mem r next ↔
      ∃ mode, DerefBindings prog mem r mode ∧
        mem.read (r.p * r.o2) =
          some (derefSource mode ⟨r.pc, r.fp⟩ (E.ofLimbs r.v3[0] r.v3[1] r.v3[2])) ∧
        next = Regs.next ⟨r.pc, r.fp⟩ := by
  constructor
  · rintro ⟨⟨mode, hfetch, hflags, h1, h3⟩, hstep⟩
    refine ⟨mode, ⟨hfetch, hflags, h1, h3⟩, ?_⟩
    rw [step_of_fetch_eq_some hfetch] at hstep
    simp only [execute, h1, h3, Option.bind_eq_bind, Option.bind_some, guard_bind_eq_some_iff,
      isInK_ofLimbs, true_and, limb_ofLimbs, Matrix.cons_val_zero] at hstep
    cases hc : mem.read (r.p * r.o2) with
    | none => rw [hc] at hstep; exact absurd hstep (by simp)
    | some c =>
      rw [hc, Option.bind_some, guard_bind_eq_some_iff] at hstep
      obtain ⟨rfl, h⟩ := hstep
      simp only [Option.pure_def, Option.some.injEq] at h
      exact ⟨rfl, h.symm⟩
  · rintro ⟨mode, ⟨hfetch, hflags, h1, h3⟩, h2, rfl⟩
    refine ⟨⟨mode, hfetch, hflags, h1, h3⟩, ?_⟩
    rw [step_of_fetch_eq_some hfetch]
    simp only [execute, h1, h3, h2, Option.bind_eq_bind, Option.bind_some,
      guard_bind_eq_some_iff, isInK_ofLimbs, true_and, limb_ofLimbs, Matrix.cons_val_zero,
      Option.pure_def]

/-! ## The adapter to the prover data -/

/-- The table's `Spec`: the row refines `DerefRefines` over the program and the image the prover
data names. -/
def DerefSpec (r : DerefRow K) (next : Regs K) (data : ProverData K) : Prop :=
  DerefRefines (programOf data) (imageOf data).2 r next

/-! ## The table -/

/-- The `DEREF` table (specification §7.4; `tables.rs:590-684`): state step, bytecode read of
`(DRF, o₁, o₂, o₃, f_pc, f_fp, 0, 0)`, the pointer read `(p, 0, 0)` at `fp·o₁`, the local read
at `fp·o₃`, and the target read at `p·o₂` carrying the flag-selected source. Returns the
pushed successor `(g·pc, fp)`. -/
def derefTable : GeneralFormalCircuit K DerefRow Regs where
  main r := do
    let next : Var Regs K := ⟨Expression.const g * r.pc, r.fp⟩
    -- `f̄ = 1 + f_pc + f_fp`: `1` at the three store modes' flags in `cell` mode, `0` otherwise.
    let fbar : Expression K := 1 + r.fpc + r.ffp
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.deref.code)
      #v[r.o1, r.o2, r.o3, r.fpc, r.ffp, 0, 0]
    memRead (r.fp * r.o1) r.r1 #v[r.p, 0, 0]
    memRead (r.fp * r.o3) r.r3 r.v3
    memRead (r.p * r.o2) r.r2
      #v[fbar * r.v3[0] + r.fpc * (Expression.const (g ^ 2) * r.pc) + r.ffp * r.fp,
         fbar * r.v3[1], fbar * r.v3[2]]
    pure next
  -- The push channels: their requirements are vacuous (Layer 5), the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Without core's `BitVec.reduceNeg` simproc, which misreads `-1 : K` (finding E6).
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The row refines the relation over the data's program and image, to the pushed successor.
  Spec := DerefSpec
  -- The honest prover's row: written from a valid step, it is bound and steps somewhere.
  -- Proved of the row built from any valid step by `derefRowOf_refines`.
  ProverAssumptions r data _ := ∃ next, DerefSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, h1, h3, h2⟩ := h_holds
    obtain ⟨_, _, _, _, _, _, _, _, hv3, _, _, _, _⟩ := h_input
    subst hv3
    -- The pulled tuple is an instruction (Layer 4): `DEREF` with the row's operands, the flags
    -- a store mode's.
    obtain ⟨mode, rfl, hflags⟩ := decode_deref_eq_some_iff.mp hdec
    obtain ⟨h4, h5⟩ := Prod.ext_iff.mp hflags
    subst h4 h5
    simp only [Vector.getElem_map] at h3 h2
    rw [storeCoords_eval] at h2
    refine (deref_refines_iff _ _ _ _).mpr ⟨mode, ⟨hfetch, rfl, h1, ?_⟩, ?_, rfl⟩
    · simpa only [Vector.getElem_map] using h3
    · simpa only [Vector.getElem_map] using h2
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The four pull guarantees, from the semantic premise: the tuple `main` emits is the
    -- fetched instruction's entry (Layer 4), and the target read carries the coordinates of
    -- the mode's source (`storeCoords_eval`).
    obtain ⟨next, h⟩ := h_assumptions
    obtain ⟨mode, ⟨hfetch, hflags, h1, h3⟩, h2, -⟩ := (deref_refines_iff _ _ _ _).mp h
    obtain ⟨_, _, _, _, _, _, _, _, hv3, _, _, _, _⟩ := h_input
    subst hv3
    obtain ⟨h4, h5⟩ := Prod.ext_iff.mp hflags
    subst h4 h5
    rw [← storeCoords_eval] at h2
    simp only [Vector.getElem_map] at h3 h2 ⊢
    exact ⟨⟨_, hfetch, decode_entry (.deref _ _ _ mode)⟩, h1, h3, h2⟩

/-! ## Rows from steps -/

/-- The row of a step that fetches `DEREF o₁ o₂ o₃ mode` from `(pc, fp)` over the image `mem`:
the registers, the operands, the mode's flags, the pointer's low limb and the local word read
back from the image, and the counts as parameters. Noncomputable: it reads the image. -/
noncomputable def derefRowOf {κ : ℕ} (mem : MemImage κ) (pc fp o1 o2 o3 : K) (mode : DerefMode)
    (r1 r2 r3 rbc : K) : DerefRow K :=
  ⟨pc, fp, o1, o2, o3, (derefFlags mode).1, (derefFlags mode).2,
    (mem.limbsAt (fp * o1))[0], mem.limbsAt (fp * o3), r1, r2, r3, rbc⟩

/-- A valid step that fetches `DEREF o₁ o₂ o₃ mode` is represented by `derefRowOf`, with any
counts: the honest prover's row refines the relation, which is `ProverAssumptions` over the
data. -/
theorem derefRowOf_refines {κ : ℕ} {prog : Program} {mem : MemImage κ} {pc fp o1 o2 o3 : K}
    {mode : DerefMode} {next : Regs K} (hfetch : prog.fetch pc = some (.deref o1 o2 o3 mode))
    (hstep : step prog mem ⟨pc, fp⟩ = some next) (r1 r2 r3 rbc : K) :
    DerefRefines prog mem (derefRowOf mem pc fp o1 o2 o3 mode r1 r2 r3 rbc) next := by
  have h := hstep
  rw [step_of_fetch_eq_some hfetch] at h
  simp only [execute, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, u, hu, v3, hv3, -⟩ := h
  have hin := guard_eq_some hu
  refine ⟨⟨mode, hfetch, rfl, ?_, ?_⟩, hstep⟩
  · show mem.read (fp * o1) = some (E.ofLimbs (mem.limbsAt (fp * o1))[0] 0 0)
    rw [MemImage.limbsAt_getElem_zero hp, ofLimbs_of_isInK hin]; exact hp
  · show mem.read (fp * o3) = some (E.ofLimbs (mem.limbsAt (fp * o3))[0]
      (mem.limbsAt (fp * o3))[1] (mem.limbsAt (fp * o3))[2])
    rw [MemImage.ofLimbs_limbsAt hv3]; exact hv3

/-- Every valid `DEREF` step has a satisfying row, from the step alone: the constraints of
`main` hold of `derefRowOf` in the row environment over the data. -/
theorem deref_step_complete {data : ProverData K} {pc fp o1 o2 o3 : K} {mode : DerefMode}
    {next : Regs K} (hfetch : (programOf data).fetch pc = some (.deref o1 o2 o3 mode))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (r1 r2 r3 rbc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((derefTable.main
        (const (derefRowOf (imageOf data).2 pc fp o1 o2 o3 mode r1 r2 r3 rbc))).operations 0) :=
  (derefTable.completeness 0 (rowEnv data) (const _)
    -- No witness slot: the row environment uses the local witnesses vacuously.
    (by simp only [circuit_norm, derefTable, memRead, bytecodeRead, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover ⟨_, derefRowOf_refines hfetch hstep r1 r2 r3 rbc⟩).1

end LeanerVM.Arithmetization
