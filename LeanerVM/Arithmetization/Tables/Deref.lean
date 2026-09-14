/-
  LeanerVM.Arithmetization.Tables.Deref

  The `DEREF` table: one Clean component per row, sound and complete for the row's functional
  specification, its bindings to the program and the image together with Layer 3's `step`.
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

**The contract.** `DerefRowBindings r data` binds the row to the program and the image: for
some store mode, the instruction at `pc` is `DEREF o₁ o₂ o₃ mode`, the row's flags are the
mode's (`derefFlags`), the pointer cell `fp·o₁` holds `p` in `K`, and the local cell `fp·o₃`
holds `word v₃`. `DerefSpec r next data` is the bindings and the step; `deref_spec_iff` expands
it, with the same mode: the target cell `p·o₂` holds `derefSource mode (pc, fp) (word v₃)`,
the local word, the return address `g²·pc`, or `fp`, and the successor is `(g·pc, fp)`;
`deref_spec_step` projects the step. The local cell is read in every mode. `DerefRowReads` is
the four pull guarantees, the target read carrying the flag-selected coordinates, and
`deref_reads_iff` identifies it with `∃ next, DerefSpec r next data` through
`storeCoords_eval` (see `LeanerVM.Arithmetization.Tables.Xor` for the template).

**The component** `derefTable` pulls the state `(pc, fp)` and pushes `(g·pc, fp)`
(`deref_output`), reads the bytecode entry `(DRF, o₁, o₂, o₃, f_pc, f_fp, 0, 0)` at `pc`, reads
the pointer cell `fp·o₁` as `(p, 0, 0)`, the local cell `fp·o₃`, and the target cell `p·o₂`,
in the order of §7.4. It returns the pushed successor, and `Spec` is `DerefSpec`;
`ProverAssumptions r data _ := ∃ next, DerefSpec r next data`.

The soundness proof needs the pulled bytecode entry to *be* an instruction: a flag pair that is
no store mode decodes to nothing, and then no `step` exists. That is what the bytecode pull
guarantees (Layer 5, `BytecodePull`), so a `DEREF` row with such a pair cannot pull its entry.

**Rows from steps.** `derefRowOf data pc fp o₁ o₂ o₃ mode r₁ r₂ r₃ rbc` is the row of a step
that fetches `DEREF o₁ o₂ o₃ mode`: the mode's flags, the pointer's low limb and the local word
read back from the image; `derefRowOf_spec`, `deref_row_exists`, `derefRow_complete` and
`deref_reads_of_constraints` are the `XOR` statements.

## Wrong readings excluded

* The pointer read carries literal zeros above its low limb (`memory_k`, `tables.rs:172-174`),
  so a pointer word outside `K` cannot balance the bus; `step` asserts `IsInK p` the same way.
* The local cell is read in every mode, `pc` and `fp` modes included (acceptance test 6):
  `memRead (fp·o₃)` is unconditional, as is the third read of `execute`, and `DerefSpec` binds
  it in every mode.
* The return address is `g²·pc`, a free `×g²` on the product coordinate (`Prod(FPC, PC, 2)`),
  never `pc + 2`.
* `DerefSpec` names the mode: the flag pair `(1, 1)` is no `derefFlags mode`, so a row
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

/-! ## Load-bearing lemmas -/

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

/-- The bytecode tuple of a `DEREF` row with a mode's flags is the entry of the instruction it
names (Layer 4). -/
theorem deref_entry (o1 o2 o3 : K) (mode : DerefMode) :
    #v[Opcode.deref.code] ++ #v[o1, o2, o3, (derefFlags mode).1, (derefFlags mode).2, 0, 0] =
      entry (.deref o1 o2 o3 mode) := rfl

/-! ## Proof helpers -/

/-- Coordinate `j` of an eight-coordinate equality. -/
private theorem coord {v w : Vector K 8} (h : v = w) (j : ℕ) (hj : j < 8) : v[j] = w[j] := by
  rw [h]

/-- A `DEREF` bytecode tuple decodes only to a `DEREF` with these operands and with a store mode
whose flags are the tuple's. -/
private theorem deref_entry_inv {o1 o2 o3 fpc ffp : K} {ins : Instr}
    (h : decode (#v[Opcode.deref.code] ++ #v[o1, o2, o3, fpc, ffp, 0, 0]) = some ins) :
    ∃ mode, ins = .deref o1 o2 o3 mode ∧ derefFlags mode = (fpc, ffp) := by
  have he : #v[Opcode.deref.code, o1, o2, o3, fpc, ffp, 0, 0] = entry ins :=
    decode_eq_some_iff.mp h
  have h0 : Opcode.deref = ins.opcode := Opcode.code_injective (by
    have := coord he 0 (by decide)
    rwa [entry_getElem_zero] at this)
  cases ins with
  | deref a b c mode =>
    refine ⟨mode, ?_, ?_⟩
    · have h1 : o1 = a := coord he 1 (by decide)
      have h2 : o2 = b := coord he 2 (by decide)
      have h3 : o3 = c := coord he 3 (by decide)
      rw [h1, h2, h3]
    · have h4 : fpc = (derefFlags mode).1 := coord he 4 (by decide)
      have h5 : ffp = (derefFlags mode).2 := coord he 5 (by decide)
      rw [h4, h5]
  | _ => simp [Instr.opcode] at h0

/-! ## The contract -/

/-- The row's bindings to the program and the image: for some store mode, the instruction at
`pc` is `DEREF o₁ o₂ o₃ mode`, the flags are the mode's, the pointer cell holds `p` in `K`,
and the local cell holds the row's word. -/
def DerefRowBindings (r : DerefRow K) (data : ProverData K) : Prop :=
  ∃ mode, (programOf data).fetch r.pc = some (.deref r.o1 r.o2 r.o3 mode) ∧
    derefFlags mode = (r.fpc, r.ffp) ∧
    (imageOf data).2.read (r.fp * r.o1) = some (E.ofLimbs r.p 0 0) ∧
    (imageOf data).2.read (r.fp * r.o3) = some (word r.v3)

/-- The functional specification of a `DEREF` row: it is bound to the program and the image,
and from its registers the machine steps to `next`. -/
def DerefSpec (r : DerefRow K) (next : Regs K) (data : ProverData K) : Prop :=
  DerefRowBindings r data ∧ step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next

/-- The four pull guarantees of the row, for the mode whose flags it carries: the fetch, the
pointer, the local word, and the target read carrying the flag-selected coordinates. -/
def DerefRowReads (r : DerefRow K) (data : ProverData K) : Prop :=
  ∃ mode, (programOf data).fetch r.pc = some (.deref r.o1 r.o2 r.o3 mode) ∧
    derefFlags mode = (r.fpc, r.ffp) ∧
    (imageOf data).2.read (r.fp * r.o1) = some (E.ofLimbs r.p 0 0) ∧
    (imageOf data).2.read (r.fp * r.o3) = some (E.ofLimbs r.v3[0] r.v3[1] r.v3[2]) ∧
    (imageOf data).2.read (r.p * r.o2) =
      some (E.ofLimbs
        (((1 : K) + r.fpc + r.ffp) * r.v3[0] + r.fpc * (g ^ 2 * r.pc) + r.ffp * r.fp)
        (((1 : K) + r.fpc + r.ffp) * r.v3[1]) (((1 : K) + r.fpc + r.ffp) * r.v3[2]))

/-- `DerefSpec`, expanded with the same mode: the bindings, the target cell `p·o₂` holds the
source the mode selects, and the successor is the fall-through `(g·pc, fp)`. -/
theorem deref_spec_iff (r : DerefRow K) (next : Regs K) (data : ProverData K) :
    DerefSpec r next data ↔
      ∃ mode, (programOf data).fetch r.pc = some (.deref r.o1 r.o2 r.o3 mode) ∧
        derefFlags mode = (r.fpc, r.ffp) ∧
        (imageOf data).2.read (r.fp * r.o1) = some (E.ofLimbs r.p 0 0) ∧
        (imageOf data).2.read (r.fp * r.o3) = some (word r.v3) ∧
        (imageOf data).2.read (r.p * r.o2) = some (derefSource mode ⟨r.pc, r.fp⟩ (word r.v3)) ∧
        next = Regs.next ⟨r.pc, r.fp⟩ := by
  unfold DerefSpec DerefRowBindings
  constructor
  · rintro ⟨⟨mode, hfetch, hflags, h1, h3⟩, hstep⟩
    refine ⟨mode, hfetch, hflags, h1, h3, ?_⟩
    rw [step_of_fetch_eq_some hfetch] at hstep
    simp only [execute, h1, h3, Option.bind_eq_bind, Option.bind_some, guard_bind_eq_some_iff,
      isInK_ofLimbs, true_and, limb_ofLimbs, Matrix.cons_val_zero] at hstep
    cases hc : (imageOf data).2.read (r.p * r.o2) with
    | none => rw [hc] at hstep; exact absurd hstep (by simp)
    | some c =>
      rw [hc, Option.bind_some, guard_bind_eq_some_iff] at hstep
      obtain ⟨rfl, h⟩ := hstep
      simp only [Option.pure_def, Option.some.injEq] at h
      exact ⟨rfl, h.symm⟩
  · rintro ⟨mode, hfetch, hflags, h1, h3, h2, rfl⟩
    refine ⟨⟨mode, hfetch, hflags, h1, h3⟩, ?_⟩
    rw [step_of_fetch_eq_some hfetch]
    simp only [execute, h1, h3, h2, Option.bind_eq_bind, Option.bind_some,
      guard_bind_eq_some_iff, isInK_ofLimbs, true_and, limb_ofLimbs, Matrix.cons_val_zero,
      Option.pure_def]

/-- The step, projected out of the specification. -/
theorem deref_spec_step {r : DerefRow K} {next : Regs K} {data : ProverData K}
    (h : DerefSpec r next data) :
    step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next :=
  h.2

/-- A row's pulls are reads of the data exactly when it is bound and steps: the target
coordinates are the mode's source (`storeCoords_eval`). -/
theorem deref_reads_iff (r : DerefRow K) (data : ProverData K) :
    DerefRowReads r data ↔ ∃ next, DerefSpec r next data := by
  constructor
  · rintro ⟨mode, hfetch, hflags, h1, h3, h2⟩
    have h4 : (derefFlags mode).1 = r.fpc := congrArg Prod.fst hflags
    have h5 : (derefFlags mode).2 = r.ffp := congrArg Prod.snd hflags
    rw [← h4, ← h5] at h2
    simp only [storeCoords_eval] at h2
    exact ⟨_, (deref_spec_iff _ _ _).mpr ⟨mode, hfetch, hflags, h1, h3, h2, rfl⟩⟩
  · rintro ⟨next, h⟩
    obtain ⟨mode, hfetch, hflags, h1, h3, h2, -⟩ := (deref_spec_iff _ _ _).mp h
    have h4 : (derefFlags mode).1 = r.fpc := congrArg Prod.fst hflags
    have h5 : (derefFlags mode).2 = r.ffp := congrArg Prod.snd hflags
    refine ⟨mode, hfetch, hflags, h1, h3, ?_⟩
    rw [← h4, ← h5]
    simp only [storeCoords_eval]
    exact h2

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
  -- The row is bound to the program and the image, and steps to the pushed successor.
  Spec := DerefSpec
  -- The semantic premise: the row is bound and steps somewhere.
  ProverAssumptions r data _ := ∃ next, DerefSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hfetch, hdec⟩, h1, h3, h2⟩ := h_holds
    obtain ⟨_, _, _, _, _, _, _, _, hv3, _, _, _, _⟩ := h_input
    subst hv3
    obtain ⟨mode, rfl, hflags⟩ := deref_entry_inv hdec
    obtain ⟨h4, h5⟩ := Prod.ext_iff.mp hflags
    subst h4 h5
    simp only [Vector.getElem_map] at h3 h2
    rw [storeCoords_eval] at h2
    refine (deref_spec_iff _ _ _).mpr ⟨mode, hfetch, rfl, h1, ?_, ?_, rfl⟩
    · simpa only [word, Vector.getElem_map] using h3
    · simpa only [word, Vector.getElem_map] using h2
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨mode, hfetch, hflags, h1, h3, h2⟩ := (deref_reads_iff _ _).mpr h_assumptions
    obtain ⟨_, _, _, _, _, _, _, _, hv3, _, _, _, _⟩ := h_input
    subst hv3
    obtain ⟨h4, h5⟩ := Prod.ext_iff.mp hflags
    subst h4 h5
    simp only [Vector.getElem_map] at h3 h2 ⊢
    exact ⟨⟨_, hfetch, by rw [deref_entry, decode_entry]⟩, h1, h3, h2⟩

/-- The returned successor: the fall-through `(g·pc, fp)`, for every environment. -/
theorem deref_output (env : Environment K) (offset : ℕ) (r : Var DerefRow K) :
    eval env ((derefTable.main r).output offset) = ⟨g * (eval env r).pc, (eval env r).fp⟩ := by
  simp only [circuit_norm, derefTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The constraints `main` emits on a row are its four pull guarantees. -/
theorem deref_reads_of_constraints {env : Environment K} {r : Var DerefRow K} {offset : ℕ}
    (h : ConstraintsHold.Soundness env ((derefTable.main r).operations offset)) :
    DerefRowReads (eval env r) env.data :=
  (deref_reads_iff _ _).mpr ⟨_, (derefTable.soundness offset env r (eval env r) rfl trivial h).1⟩

/-! ## Rows from steps -/

/-- The row of a step that fetches `DEREF o₁ o₂ o₃ mode` from `(pc, fp)`: the registers, the
operands, the mode's flags, the pointer's low limb and the local word read back from the image,
and the counts as parameters. Noncomputable: it reads the image. -/
noncomputable def derefRowOf (data : ProverData K) (pc fp o1 o2 o3 : K) (mode : DerefMode)
    (r1 r2 r3 rbc : K) : DerefRow K :=
  ⟨pc, fp, o1, o2, o3, (derefFlags mode).1, (derefFlags mode).2,
    (limbsAt (imageOf data).2 (fp * o1))[0], limbsAt (imageOf data).2 (fp * o3), r1, r2, r3, rbc⟩

/-- A valid step that fetches `DEREF o₁ o₂ o₃ mode` is represented by `derefRowOf`, with any
counts. -/
theorem derefRowOf_spec {data : ProverData K} {pc fp o1 o2 o3 : K} {mode : DerefMode}
    {next : Regs K} (hfetch : (programOf data).fetch pc = some (.deref o1 o2 o3 mode))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (r1 r2 r3 rbc : K) :
    DerefSpec (derefRowOf data pc fp o1 o2 o3 mode r1 r2 r3 rbc) next data := by
  have h := hstep
  rw [step_of_fetch_eq_some hfetch] at h
  simp only [execute, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, u, hu, v3, hv3, -⟩ := h
  have hin := guard_eq_some hu
  refine ⟨⟨mode, hfetch, rfl, ?_, ?_⟩, hstep⟩
  · show (imageOf data).2.read (fp * o1) =
      some (E.ofLimbs (limbsAt (imageOf data).2 (fp * o1))[0] 0 0)
    rw [limbsAt_getElem_zero hp, ofLimbs_of_isInK hin]; exact hp
  · show (imageOf data).2.read (fp * o3) = some (word (limbsAt (imageOf data).2 (fp * o3)))
    rw [word_limbsAt hv3]; exact hv3

/-- A valid step that fetches `DEREF o₁ o₂ o₃ mode` admits a row with the same registers,
operands and the mode's flags, and any counts. -/
theorem deref_row_exists {data : ProverData K} {pc fp o1 o2 o3 : K} {mode : DerefMode}
    {next : Regs K} (hfetch : (programOf data).fetch pc = some (.deref o1 o2 o3 mode))
    (hstep : step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next) (r1 r2 r3 rbc : K) :
    ∃ p v3, DerefSpec ⟨pc, fp, o1, o2, o3, (derefFlags mode).1, (derefFlags mode).2, p, v3,
      r1, r2, r3, rbc⟩ next data :=
  ⟨_, _, derefRowOf_spec hfetch hstep r1 r2 r3 rbc⟩

/-- A row with the semantic premise satisfies the constraints of `main` in the row environment
over its data. -/
theorem derefRow_complete {r : DerefRow K} {data : ProverData K}
    (h : ∃ next, DerefSpec r next data) :
    ConstraintsHold.Completeness (rowEnv data) ((derefTable.main (const r)).operations 0) :=
  (derefTable.completeness 0 (rowEnv data) (const r)
    (by simp only [circuit_norm, derefTable, memRead, bytecodeRead, -BitVec.reduceNeg]) r
    ProvableType.eval_const_prover h).1

end LeanerVM.Arithmetization
