/-
  LeanerVM.Arithmetization.Tables.Deref

  The `DEREF` table: one Clean component per row, sound and complete for `step`.
  A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Channels
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

**The component** `derefTable` pulls the state `(pc, fp)` and pushes `(g·pc, fp)`, reads the
bytecode entry `(DRF, o₁, o₂, o₃, f_pc, f_fp, 0, 0)` at `pc`, reads the pointer cell `fp·o₁` as
`(p, 0, 0)`, the local cell `fp·o₃`, and the target cell `p·o₂`, in the order of §7.4. It
returns the pushed successor, and `Spec` is
`step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next` (see
`LeanerVM.Arithmetization.Tables.Xor` for the template).

The soundness proof needs the pulled bytecode entry to *be* an instruction: a flag pair that is
no store mode decodes to nothing, and then no `step` exists. That is what the bytecode pull
guarantees (Layer 5, `BytecodePull`), so a `DEREF` row with such a pair cannot pull its entry.

## Wrong readings excluded

* The pointer read carries literal zeros above its low limb (`memory_k`, `tables.rs:172-174`),
  so a pointer word outside `K` cannot balance the bus; `step` asserts `IsInK p` the same way.
* The local cell is read in every mode, `pc` and `fp` modes included (acceptance test 6):
  `memRead (fp·o₃)` is unconditional, as is the third read of `execute`.
* The return address is `g²·pc`, a free `×g²` on the product coordinate (`Prod(FPC, PC, 2)`),
  never `pc + 2`.
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

/-- `ofK a` is the word with limbs `(a, 0, 0)`. -/
theorem ofK_eq_ofLimbs (a : K) : ofK a = E.ofLimbs a 0 0 :=
  E.ext fun i ↦ by fin_cases i <;> simp

/-- A word with zero upper limbs lies in `K`. -/
theorem isInK_ofLimbs (c : K) : IsInK (E.ofLimbs c 0 0) := ⟨by simp, by simp⟩

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
  -- The row is a step: from its registers the machine steps to the pushed successor.
  Spec r next data := step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next
  -- The honest row: the operands and flags are the fetched instruction's, the pointer cell
  -- holds `p` in `K`, and the local and target cells hold the image's words, the target the
  -- flag-selected source.
  ProverAssumptions r data _ :=
    ∃ mode, (programOf data).fetch r.pc = some (.deref r.o1 r.o2 r.o3 mode) ∧
      derefFlags mode = (r.fpc, r.ffp) ∧
      (imageOf data).2.read (r.fp * r.o1) = some (E.ofLimbs r.p 0 0) ∧
      (imageOf data).2.read (r.fp * r.o3) = some (E.ofLimbs r.v3[0] r.v3[1] r.v3[2]) ∧
      (imageOf data).2.read (r.p * r.o2) =
        some (E.ofLimbs
          ((1 + r.fpc + r.ffp) * r.v3[0] + r.fpc * (g ^ 2 * r.pc) + r.ffp * r.fp)
          ((1 + r.fpc + r.ffp) * r.v3[1]) ((1 + r.fpc + r.ffp) * r.v3[2]))
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
    rw [step_of_fetch_eq_some hfetch]
    simp only [execute, guard, h1, h2, h3, isInK_ofLimbs, storeCoords_eval, limb_ofLimbs,
      Matrix.cons_val_zero, ite_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Regs.next]
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨mode, hfetch, hflags, h1, h3, h2⟩ := h_assumptions
    obtain ⟨_, _, _, _, _, _, _, _, hv3, _, _, _, _⟩ := h_input
    subst hv3
    obtain ⟨h4, h5⟩ := Prod.ext_iff.mp hflags
    subst h4 h5
    simp only [Vector.getElem_map] at h3 h2 ⊢
    exact ⟨⟨_, hfetch, by rw [deref_entry, decode_entry]⟩, h1, h3, h2⟩

end LeanerVM.Arithmetization
