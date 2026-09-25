/-
  LeanerVM.Semantics.Step

  The registers, the source a `DEREF` stores, and one step of the machine.
-/

module

public import LeanerVM.Semantics.Blake2s
public import LeanerVM.Semantics.Instruction

/-!
# One step of the machine

leanISA roadmap Layer 3 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category A: written from specification §2
(`doc/leanvm/body/02-vm-specification.tex`; the registers `:16-20`, the execution loop
`:26-35`, the operands `:49-52`, the instruction table `:54-68`, `DEREF` `:71-81`, `JUMP`
`:86`, `BLAKE2S` `:90-93`) before the Rust executor (`crates/lean_vm/src/cpu/execute.rs`) was
opened; the diff against the executor is recorded in `docs/roadmap/leanisa-status.md`. Where §2
is silent the roadmap's pinned conventions decide: `DEREF` reads its local cell in every mode
(specification §7.4, acceptance test 6), and the halting test that keeps the sentinel from ever
being executed belongs to the loop, `LeanerVM.Semantics.Execution` (acceptance test 5).

**The registers** are two `K` elements, `pc` and `fp`, the pair `Regs K`; the structure is
parametric in the field so that the bus of Layer 5 carries the same pair over `Expression K`.
Every instruction but a taken `JUMP` advances to the fall-through successor
`Regs.next r = (g · pc, fp)`, the next bytecode slot in the same frame (§2, execution loop
step 2).

**One step** is `step prog L r = prog.fetch r.pc >>= execute L r`: fetch the instruction at
`pc` (`Program.fetch`), then `execute` it against the committed image `L`: read the cells it
names (`MemImage.read`, an operand `o` naming `fp · o`), check the instruction's relation on
the values read, and return the next registers. A failed fetch, a failed read, or a false
relation is `none`. Values are only ever read and compared: the image is fixed before
execution, so "`[o_C] = [o_A] + [o_B]`" is a check on three words, and a constraint row of
Layer 6 corresponds to a step by unfolding `execute` and `executeWith`. The arms are written
once, in `executeWith` over a named reader; `execute L r` is `executeWith L.read r`, and the
computable carrier of `LeanerVM.Semantics.Executable` is the same arms at a computable reader.

The arms of `executeWith`, in the order of §2's table:

* `XOR`, `MUL_NATIVE`: `[o_C] = [o_A] + [o_B]`, respectively `[o_A] · [o_B]`, in `E`.
* `SET_CONSTANT`: `[o] = k`.
* `DEREF`: the pointer `p = [o₁]` lies in `K`, and the cell `mem[p · o₂]` holds the source
  `derefSource mode`: the local cell `[o₃]`, the return address `g² · pc`, or `fp`.
* `JUMP`: `c = [o_c]`, `d = [o_d]`, `f = [o_f]` all lie in `K`, taken or not; the successor is
  `(d, f)` when `c ≠ 0` and `Regs.next` otherwise.
* `BLAKE2S`: the nine cells `[o_{m_i}]`, `[o_cv]`, `[g · o_cv]`, `[o_out]`, `[g · o_out]`,
  `[o_md]` satisfy `CompressCells` (`LeanerVM.Semantics.Blake2s`).

## Wrong readings excluded

* The successor of `pc` is `g · pc`, never `pc + 1` (acceptance test 3): `1 + 1 = 0` in `K`.
* `DEREF` reads three cells in every mode; the local cell `[o₃]` must be in range even when
  the mode ignores its value (acceptance test 6).
* `JUMP`'s three membership assertions are unconditional: `c = 0` with `d ∉ K` is `none`
  (acceptance test 7).
* All nine `BLAKE2S` cells are canonical, the two output cells included, through
  `CompressCells` (acceptance test 12).
* There is no second semantics. The six arms exist once, in `executeWith`; the carrier only
  changes the reader. The executor's write-once bookkeeping, back-solving, hints, and
  deferrals are witness generation, specified later against `step` (acceptance test 19).
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## Registers -/

/-- The two registers (specification §2), over a field `F`: `Regs K` is the machine's register
pair, and `Regs (Expression K)` a table row's, so that one structure serves the semantics and
the state channel of the bus (roadmap Layer 5). -/
structure Regs (F : Type) where
  /-- The program counter: the address of the instruction to execute. -/
  pc : F
  /-- The frame pointer: the base of the current frame, an operand `o` naming `fp · o`. -/
  fp : F
  deriving Repr

/-- Register equality is decided field by field. Not derived: the derived instance decides the
second field under `h ▸` for the first, whose `Eq.rec` makes the kernel compare two register
values by definitional unfolding instead of evaluation, and `g * 1 = g ^ 1` then never
decides (status finding E5). -/
instance {F : Type} [DecidableEq F] : DecidableEq (Regs F) := fun x y ↦
  decidable_of_iff (x.pc = y.pc ∧ x.fp = y.fp) (by cases x; cases y; simp)

/-- The fall-through successor `(g · pc, fp)`: the next bytecode slot, same frame (§2,
execution loop step 2). -/
def Regs.next (r : Regs K) : Regs K := ⟨g * r.pc, r.fp⟩

/-! ## `DEREF` -/

/-- The value a `DEREF` stores, by mode: the local cell `[o₃]`, the return address `g² · pc`,
or the frame pointer `fp`, the registers embedded in `E` (§2, `src(mode)`). -/
def derefSource : DerefMode → Regs K → E → E
  | .cell, _, v3 => v3
  | .pc, r, _ => ofK (g ^ 2 * r.pc)
  | .fp, r, _ => ofK r.fp

/-! ## The step -/

/-- The six arms of one instruction over a named reader `read`: read the cells the instruction
names, check its relation, and return the next registers; `none` on a failed read or a false
relation (§2, execution loop step 2, "execute inst"). The machine's step is `execute`, this
function at the image's reader `L.read`; the computable carrier (`LeanerVM.Semantics.Executable`)
instantiates the same arms with its own reader, so the arms exist once (acceptance test 19). -/
def executeWith (read : K → Option E) (r : Regs K) : Instr → Option (Regs K)
  | .xor oA oB oC => do
    let vA ← read (r.fp * oA)
    let vB ← read (r.fp * oB)
    let vC ← read (r.fp * oC)
    guard (vC = vA + vB)
    pure r.next
  | .mulNative oA oB oC => do
    let vA ← read (r.fp * oA)
    let vB ← read (r.fp * oB)
    let vC ← read (r.fp * oC)
    guard (vC = vA * vB)
    pure r.next
  | .setConstant o k => do
    let v ← read (r.fp * o)
    guard (v = k)
    pure r.next
  | .deref o1 o2 o3 mode => do
    let p ← read (r.fp * o1)
    guard (IsInK p)
    let v3 ← read (r.fp * o3)
    let v2 ← read (p.limb 0 * o2)
    guard (v2 = derefSource mode r v3)
    pure r.next
  | .jump oc od of => do
    let c ← read (r.fp * oc)
    let d ← read (r.fp * od)
    let f ← read (r.fp * of)
    guard (IsInK c ∧ IsInK d ∧ IsInK f)
    pure (if c = 0 then r.next else ⟨d.limb 0, f.limb 0⟩)
  | .blake2s om ocv oout omd => do
    let m0 ← read (r.fp * om 0)
    let m1 ← read (r.fp * om 1)
    let m2 ← read (r.fp * om 2)
    let m3 ← read (r.fp * om 3)
    let cv0 ← read (r.fp * ocv)
    let cv1 ← read (r.fp * (g * ocv))
    let out0 ← read (r.fp * oout)
    let out1 ← read (r.fp * (g * oout))
    let md ← read (r.fp * omd)
    guard (CompressCells ![m0, m1, m2, m3] cv0 cv1 out0 out1 md)
    pure r.next

/-- Execute one instruction from registers `r` over the committed image `L`: the arms of
`executeWith` at the image's reader `MemImage.read`, which is what makes the specification
noncomputable (§2, execution loop step 2). -/
noncomputable def execute {κ : ℕ} (L : MemImage κ) (r : Regs K) : Instr → Option (Regs K) :=
  executeWith L.read r

/-- One step of the machine: fetch the instruction at `pc` and execute it (§2, execution loop
steps 1–2); `none` when the counter fetches nothing. -/
noncomputable def step {κ : ℕ} (prog : Program) (L : MemImage κ) (r : Regs K) :
    Option (Regs K) :=
  prog.fetch r.pc >>= execute L r

/-! ## Load-bearing lemmas -/

/-- A counter that fetches nothing steps nowhere. -/
theorem step_eq_none_of_fetch_eq_none {κ : ℕ} {prog : Program} {L : MemImage κ} {r : Regs K}
    (h : prog.fetch r.pc = none) : step prog L r = none := by
  rw [step, h]; rfl

/-- A step from a counter that fetches `ins` executes `ins`. -/
theorem step_of_fetch_eq_some {κ : ℕ} {prog : Program} {L : MemImage κ} {r : Regs K}
    {ins : Instr} (h : prog.fetch r.pc = some ins) : step prog L r = execute L r ins := by
  rw [step, h]; rfl

/-- A step that fetches `ins` and reaches `next` executes `ins` to `next`: the one join between
a program's step and an instruction's execution. The tables of the arithmetization (Layer 6)
are stated over `execute`, program-free as leanVM's are, and Layer 10 composes them with
`Program.fetch` through this lemma. -/
theorem execute_of_step {κ : ℕ} {prog : Program} {L : MemImage κ} {r : Regs K} {ins : Instr}
    {next : Regs K} (hfetch : prog.fetch r.pc = some ins) (hstep : step prog L r = some next) :
    execute L r ins = some next := by
  rwa [step_of_fetch_eq_some hfetch] at hstep

end
end LeanerVM.Semantics
