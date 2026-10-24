/-
  LeanVM.Spec.Isa

  leanISA, the leanVM instruction set: memory, instructions, programs, one step, valid
  executions; and the encoding of an instruction as sixteen `K` slots.
-/

module

public import LeanVM.Spec.Field
public import LeanVM.Spec.Keccak

/-!
# leanISA

The leanVM instruction set, from §2 of the leanVM specification
(`doc/leanvm/body/02-vm-specification.tex`) at `94ee12ff6b2a3d42ba8328e22d09443692e4800b` (branch
`main`).

Words are elements of `E = K[y]/(y³ + y + 1)`, `K = GF(2^64)`. Addresses are powers of the
generator `g` of `K*`: memory word `i` and bytecode slot `i` both sit at `g^i`. The machine has two
registers, `pc` and `fp`, and halts in the final state `(g^(N_prog - 1), 1)`: the last slot in
`main`'s frame. The memory is fixed before the run and only read: every instruction checks a
relation on the words it reads, so all nondeterminism is the choice of the memory.

The encoding of an instruction as sixteen `K` slots (specification §8.1) is how the verifier
receives a program.
-/

namespace LeanVM.Parameters

@[expose] public section

/-! ## Opcodes -/

/-- The six instructions, in bus-code order (`tables.rs:99-104`). -/
inductive Opcode
  | xor
  | mulNative
  | setConstant
  | deref
  | jump
  | keccak
  deriving DecidableEq, Repr

/-- The bus code of an opcode: `g^0, …, g^5` in constructor order (specification §6.4). -/
def Opcode.code : Opcode → K
  | .xor => gpow 0
  | .mulNative => gpow 1
  | .setConstant => gpow 2
  | .deref => gpow 3
  | .jump => gpow 4
  | .keccak => gpow 5

/-! ## Size bounds (specification §2, §6.2) -/

/-- The least memory log-size, `2^16` cells (`cpu/mod.rs:41`, `MIN_LOG_MEM`). -/
def minLogMem : ℕ := 16

/-- The greatest memory log-size, `2^32` cells (`cpu/mod.rs:42`, `MAX_LOG_MEM`). -/
def maxLogMem : ℕ := 32

/-- The greatest bytecode log-size, in instructions (`crates/verifier/src/layout.rs:487`;
`verifier.py:975`). -/
def maxLogBytecode : ℕ := 32

end
end LeanVM.Parameters

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-! ## Memory -/

open Classical in
/-- The index of an address: `some i` when `a = g^i` with `i < 2^κ`, otherwise `none`. -/
noncomputable def gLog? (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  if h : ∃ i : Fin (2 ^ κ), a = gpow i then some (Classical.choose h) else none

/-- A memory of `2^κ` words, by index. -/
abbrev MemImage (κ : ℕ) : Type := Fin (2 ^ κ) → E

/-- The word at address `a`, if `a` is an address. -/
noncomputable def MemImage.read {κ : ℕ} (L : MemImage κ) (a : K) : Option E :=
  (gLog? κ a).map L

/-- The public input: 256 bits, as four `K` lanes. -/
structure PublicInput where
  /-- The four lanes. -/
  lanes : Fin 4 → K
  deriving DecidableEq

/-- Memory word `0` holds `lane₀ + lane₁·y`. -/
def PublicInput.word0 (p : PublicInput) : E := E.ofLimbs (p.lanes 0) (p.lanes 1) 0

/-- Memory word `1` holds `lane₂ + lane₃·y`. -/
def PublicInput.word1 (p : PublicInput) : E := E.ofLimbs (p.lanes 2) (p.lanes 3) 0

/-! ## Instructions and programs

An operand `o` names the word at `fp · o`, written `[o]`. -/

/-- What a `DEREF` stores: a local word, the return address, or the frame pointer. -/
inductive DerefMode
  | cell
  | pc
  | fp
  deriving DecidableEq, Repr

/-- The six instructions. -/
inductive Instr
  /-- `[o_C] = [o_A] + [o_B]`. -/
  | xor (oA oB oC : K)
  /-- `[o_C] = [o_A] · [o_B]`. -/
  | mulNative (oA oB oC : K)
  /-- `[o] = k`. -/
  | setConstant (o : K) (k : E)
  /-- `[o₁]` is in `K`, and the word at address `[o₁] · o₂` is the source `mode` selects
  (`derefSource`); `[o₃]` is read in every mode. -/
  | deref (o1 o2 o3 : K) (mode : DerefMode)
  /-- `[o_c]`, `[o_d]`, `[o_f]` are in `K`; jump to `([o_d], [o_f])` if `[o_c] ≠ 0`. -/
  | jump (oc od of : K)
  /-- One Keccak-f[1600] permutation of a state held in thirteen cells: the cells
  `[o_m₀], …, [o_m₃]`, `[g^k · o_tail]` (`k < 4`), `[o_b8]`, `[g^k · o_cap]` (`k < 4`), read in the
  layout `inOdd`, permute to the cells `[g^k · o_out]` (`k < 13`), written in the layout `outOdd`
  (`KeccakCells`). -/
  | keccak (om : Fin 4 → K) (otail ob8 ocap oout : K) (inOdd outOdd : Bool)
  deriving DecidableEq

/-- The opcode of an instruction. -/
def Instr.opcode : Instr → Opcode
  | .xor .. => .xor
  | .mulNative .. => .mulNative
  | .setConstant .. => .setConstant
  | .deref .. => .deref
  | .jump .. => .jump
  | .keccak .. => .keccak

/-- A program: `2^logSize` instructions, instruction `i` at address `g^i`. -/
structure Program where
  /-- The log of the number of instructions. -/
  logSize : ℕ
  /-- At most `2^32` instructions. -/
  logSize_le : logSize ≤ maxLogBytecode
  /-- The instructions. -/
  code : Fin (2 ^ logSize) → Instr

/-- The instruction at address `pc`. -/
noncomputable def Program.fetch (prog : Program) (pc : K) : Option Instr :=
  (gLog? prog.logSize pc).map prog.code

/-! ## `KECCAK`

How the 25 lanes of a Keccak state are held in thirteen memory words, two lanes to a word, in the
words' limbs `0` and `1`, the `y²` limb zero (specification §2, the `KECCAK` paragraph;
`_keccak_cell_lanes`, `verifier.py:871-883`; `cell_lanes`, `crates/leanvm_core/src/keccak.rs:68-89`):

* even layout: cell `c < 8` holds lanes `(2c, 2c + 1)`, cell `8` holds `(16, ·)`;
* odd layout: cell `0` holds `(·, 0)`, cell `1 ≤ c ≤ 8` holds `(2c − 1, 2c)`;
* both: cell `9 ≤ c < 13` holds `(2c − 1, 2c)`.

A limb `·` holds no lane: it is ignored when read and zero when written. -/

/-- The lanes cell `c` holds in limbs `0` and `1`, in the layout `odd` (`_keccak_cell_lanes`,
`verifier.py:875-883`); `none` marks a limb that holds no lane. -/
def cellLanes (odd : Bool) (c : ℕ) : Option ℕ × Option ℕ :=
  if 9 ≤ c ∨ (odd ∧ 1 ≤ c) then (some (2 * c - 1), some (2 * c))
  else if odd then (none, some 0)
  else if c = 8 then (some 16, none)
  else (some (2 * c), some (2 * c + 1))

/-- The state thirteen cells hold in the layout `odd`: lane `l` is the limb of the cell that holds
it (`state_of_cells`, `crates/leanvm_core/src/keccak.rs:91-103`). -/
def stateOfCells (cells : Fin 13 → E) (odd : Bool) : KState :=
  (List.finRange 13).foldl (fun s (c : Fin 13) ↦
    let (lo, hi) := cellLanes odd c.val
    let s := match lo with
      | some l => s.setIfInBounds l (cells c |>.limb 0).lane
      | none => s
    match hi with
      | some l => s.setIfInBounds l (cells c |>.limb 1).lane
      | none => s) (Vector.replicate 25 0)

/-- The thirteen cells holding a state in the layout `odd`, a limb holding no lane zero, the `y²`
limb zero (`cells_of_state`, `crates/leanvm_core/src/keccak.rs:105-116`). -/
def cellsOfState (s : KState) (odd : Bool) (c : Fin 13) : E :=
  let limb := fun (l : Option ℕ) ↦ match l with
    | some l => K.ofLane (Keccak.lane s l)
    | none => 0
  E.ofLimbs (limb (cellLanes odd c).1) (limb (cellLanes odd c).2) 0

/-- What `KECCAK` checks: the thirteen cells read have no `y²` term, and the thirteen written are
the cells, in the layout `outOdd`, of Keccak-f[1600] of the state the cells read hold in the
layout `inOdd`. -/
def KeccakCells (input : Fin 13 → E) (inOdd : Bool) (output : Fin 13 → E) (outOdd : Bool) :
    Prop :=
  (∀ c, IsCanonical128 (input c)) ∧
    ∀ c, output c = cellsOfState (keccakF (stateOfCells input inOdd)) outOdd c

/-- `KeccakCells` is decidable. -/
instance {input : Fin 13 → E} {inOdd : Bool} {output : Fin 13 → E} {outOdd : Bool} :
    Decidable (KeccakCells input inOdd output outOdd) := by
  unfold KeccakCells; infer_instance

/-- The address of read cell `c` relative to the frame: `o_m₀, …, o_m₃`, then `g^k · o_tail`
(`k < 4`), `o_b8`, then `g^k · o_cap` (`k < 4`) (`_flushes_keccak`'s `address`,
`verifier.py:906-911`). -/
def keccakInOffset (om : Fin 4 → K) (otail ob8 ocap : K) (c : Fin 13) : K :=
  if h : c.val < 4 then om ⟨c.val, h⟩
  else if c.val < 8 then g ^ (c.val - 4) * otail
  else if c.val = 8 then ob8
  else g ^ (c.val - 9) * ocap

/-- Read the thirteen words at the frame-relative offsets `offset c`, in order; `none` if any read
fails. -/
def readCells (read : K → Option E) (fp : K) (offset : Fin 13 → K) : Option (Fin 13 → E) :=
  (List.finRange 13).foldr (fun c acc ↦ do
    let v ← read (fp * offset c)
    let rest ← acc
    pure fun c' ↦ if c' = c then v else rest c') (some fun _ ↦ 0)

/-! ## One step -/

/-- The registers: the program counter and the frame pointer. -/
structure Regs (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  deriving Repr

/-- Register equality is decided field by field. Not derived: the derived instance decides the
second field under `h ▸` for the first, whose `Eq.rec` makes the kernel compare two register
values by definitional unfolding instead of evaluation, and `g * 1 = g ^ 1` then never
decides. -/
instance {F : Type} [DecidableEq F] : DecidableEq (Regs F) := fun x y ↦
  decidable_of_iff (x.pc = y.pc ∧ x.fp = y.fp) (by cases x; cases y; simp)

/-- The next instruction, same frame: `(g · pc, fp)`. -/
def Regs.next (r : Regs K) : Regs K := ⟨g * r.pc, r.fp⟩

/-- What a `DEREF` stores: the local word `[o₃]`, the return address `g² · pc`, or `fp`. -/
def derefSource : DerefMode → Regs K → E → E
  | .cell, _, v3 => v3
  | .pc, r, _ => ofK (g ^ 2 * r.pc)
  | .fp, r, _ => ofK r.fp

/-- Execute an instruction with the memory reader `read`: read its words, check its relation, and
return the next registers; `none` if a read or a check fails. -/
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
  | .keccak om otail ob8 ocap oout inOdd outOdd => do
    let input ← readCells read r.fp (keccakInOffset om otail ob8 ocap)
    let output ← readCells read r.fp fun c ↦ g ^ c.val * oout
    guard (KeccakCells input inOdd output outOdd)
    pure r.next

/-- Execute an instruction on the memory `L`. -/
noncomputable def execute {κ : ℕ} (L : MemImage κ) (r : Regs K) : Instr → Option (Regs K) :=
  executeWith L.read r

/-- One step: fetch the instruction at `pc` and execute it. -/
noncomputable def step {κ : ℕ} (prog : Program) (L : MemImage κ) (r : Regs K) :
    Option (Regs K) :=
  prog.fetch r.pc >>= execute L r

/-! ## Valid executions -/

/-- The machine starts at `(pc, fp) = (1, 1)`. -/
def Regs.initial : Regs K := ⟨1, 1⟩

/-- The last bytecode slot, `g^(2^logSize − 1)`, the final state's `pc`. -/
def Program.finalPc (prog : Program) : K := gpow (2 ^ prog.logSize - 1)

/-- The final state `(finalPc, 1)`: the last slot in `main`'s frame, `(g^(N_prog - 1), g^0)`. The
machine halts there. -/
def Regs.final (prog : Program) : Regs K := ⟨prog.finalPc, 1⟩

/-- `n` steps from `r`, halting in the final state: `none` if a step fails or the machine halts
first. The machine halts when both registers are the final state's (specification §2, the loop's
last step; `crates/leanvm_core/src/cpu/execute.rs:551-562`): the last slot reached in another
frame executes like any other slot, and a step that falls through it, to `g^(2^logSize)`, which
is no bytecode address, fails. -/
noncomputable def run {κ : ℕ} (prog : Program) (L : MemImage κ) : ℕ → Regs K → Option (Regs K)
  | 0, r => some r
  | n + 1, r => if r = Regs.final prog then none else step prog L r >>= run prog L n

/-- An execution: a memory of `2^κ` words and a number of steps. -/
structure Trace (prog : Program) where
  /-- The log of the memory size. -/
  κ : ℕ
  /-- The memory. -/
  image : MemImage κ
  /-- The number of steps. -/
  steps : ℕ

/-- The memory has between `2^16` and `2^32` words and holds the public input in words `0`, `1`. -/
def HasPublicBoundary {prog : Program} (input : PublicInput) (t : Trace prog) : Prop :=
  minLogMem ≤ t.κ ∧ t.κ ≤ maxLogMem ∧
    t.image.read (gpow 0) = some input.word0 ∧ t.image.read (gpow 1) = some input.word1

/-- **A valid execution** of `prog` on `input`: the memory holds the public input, and `t.steps`
steps from `(1, 1)` halt in the final state `(finalPc, 1)`. -/
def ValidExecution (prog : Program) (input : PublicInput) (t : Trace prog) : Prop :=
  HasPublicBoundary input t ∧ run prog t.image t.steps Regs.initial = some (Regs.final prog)

/-! ## Instruction counts -/

/-- The number of instructions of opcode `op` executed in `n` steps from `r`, stepping as `run`
does; the count stops at a step that fails. -/
noncomputable def runCount {κ : ℕ} (prog : Program) (L : MemImage κ) (op : Opcode) :
    ℕ → Regs K → ℕ
  | 0, _ => 0
  | n + 1, r =>
    match prog.fetch r.pc, step prog L r with
    | some ins, some r' => (if ins.opcode = op then 1 else 0) + runCount prog L op n r'
    | _, _ => 0

/-- The number of instructions of opcode `op` an execution executes. -/
noncomputable def Trace.count {prog : Program} (t : Trace prog) (op : Opcode) : ℕ :=
  runCount prog t.image op t.steps Regs.initial

end
end LeanVM.Semantics

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## The bytecode encoding (specification §8.1) -/

/-- The `DEREF` store-mode flags `(f_pc, f_fp)`: `cell ↦ (0, 0)`, `pc ↦ (1, 0)`, `fp ↦ (0, 1)`
(`isa.rs:68-75`; specification §7.4). -/
def derefFlags : DerefMode → K × K
  | .cell => (0, 0)
  | .pc => (1, 0)
  | .fp => (0, 1)

/-- A layout flag as the bytecode carries it: `0` or `1` (`flag`, `cpu/layout.rs:311`). -/
def flagK (b : Bool) : K := if b then 1 else 0

/-- The bus entry of an instruction, `(opcode, op₁, …, op₁₀)`: slots 3 to 13 of specification
§8.1, the eleven public columns of `bytecode_columns` (`cpu/layout.rs:288-367`): offsets as
g-powers, a `SET` immediate as its three limbs, the `DEREF` store-mode flags and `KECCAK`'s
layout flags as `0` or `1`, unused slots zero. -/
def entry : Instr → Vector K 11
  | .xor oA oB oC => #v[Opcode.xor.code, oA, oB, oC, 0, 0, 0, 0, 0, 0, 0]
  | .mulNative oA oB oC => #v[Opcode.mulNative.code, oA, oB, oC, 0, 0, 0, 0, 0, 0, 0]
  | .setConstant o k =>
      #v[Opcode.setConstant.code, o, k.limb 0, k.limb 1, k.limb 2, 0, 0, 0, 0, 0, 0]
  | .deref o1 o2 o3 mode =>
      #v[Opcode.deref.code, o1, o2, o3, (derefFlags mode).1, (derefFlags mode).2, 0, 0, 0, 0, 0]
  | .jump oc od of => #v[Opcode.jump.code, oc, od, of, 0, 0, 0, 0, 0, 0, 0]
  | .keccak om otail ob8 ocap oout inOdd outOdd =>
      #v[Opcode.keccak.code, om 0, om 1, om 2, om 3, otail, ob8, ocap, oout, flagK inOdd,
        flagK outOdd]

/-- The sixteen slots of an instruction (specification §8.1; `BYTECODE_PUBLIC_SLOT = 3`,
`leaf.rs:770`): the entry at slots 3 to 13, zero elsewhere. -/
def encodeSlots (i : Instr) : Vector K 16 :=
  let e := entry i
  #v[0, 0, 0, e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], e[8], e[9], e[10], 0, 0]

end
end LeanVM.Arithmetization
