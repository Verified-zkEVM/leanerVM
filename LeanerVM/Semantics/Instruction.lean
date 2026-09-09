/-
  LeanerVM.Semantics.Instruction

  Instructions, programs, and instruction fetch.
-/

module

public import LeanerVM.Parameters.Isa
public import LeanerVM.Semantics.Memory

/-!
# Instructions and programs

leanISA roadmap Layer 2 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category B: the instruction set is specification
§2 (`doc/leanvm/body/02-vm-specification.tex:54-68`, the table; `:71-79`, the `DEREF` store
modes), matching `crates/lean_vm/src/cpu/isa.rs:6-66` (`Op`, `DerefMode`); the bytecode is
`2 ^ κ_bc` instructions with `κ_bc ≤ 32`, addressed like memory (§2 `:16,22`; §6.4
`06-bus-interactions.tex:90`; `cpu/mod.rs:158-159`).

An operand is a `K` element: the `g`-power `o = g ^ j` naming the frame cell at `fp · o` (§2
"Operands and addressing"), except that `SET_CONSTANT`'s immediate is one word `k ∈ E`, whose
three lanes are the operands `k₀, k₁, k₂` of the specification's table (`isa.rs:17-23`, one
`F192`). The executor keeps operands as `u32` exponents (status finding R1); the machine's
operands are the field elements, so an operand that is not a `g`-power is expressible and names
no valid cell.

`Program.fetch` reads the instruction at a program counter through the same bounded logarithm
as memory: `pc = g ^ i` with `i < 2 ^ logSize` fetches instruction `i` and every other `pc`
fetches nothing. The halting test of Layer 3 runs before the fetch, so a valid execution never
fetches the sentinel slot `g ^ (2 ^ logSize - 1)` (roadmap acceptance test 5). The store-mode
flag pair `(1, 1)` has no constructor: it is excluded by the public program's decoder
(Layer 4), not by a constraint (acceptance test 18).
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## Instructions -/

/-- The source a `DEREF` stores: the local cell `[o₃]`, the return address `g² · pc`, or `fp`
(specification §2; `isa.rs:58-66`, flags `(f_pc, f_fp) = (0,0), (1,0), (0,1)`). -/
inductive DerefMode
  | cell
  | pc
  | fp
  deriving DecidableEq, Repr

/-- The six instructions with their operands, in the order of the specification's table (§2).
`[o]` is the word at `fp · o`. -/
inductive Instr
  /-- `XOR [o_A, o_B, o_C]`: `[o_C] = [o_A] + [o_B]` in `E`. -/
  | xor (oA oB oC : K)
  /-- `MUL_NATIVE [o_A, o_B, o_C]`: `[o_C] = [o_A] · [o_B]` in `E`. -/
  | mulNative (oA oB oC : K)
  /-- `SET_CONSTANT [o, k₀, k₁, k₂]`: `[o] = k`, the immediate `k = k₀ + k₁·y + k₂·y²`. -/
  | setConstant (o : K) (k : E)
  /-- `DEREF [o₁, o₂, o₃; mode]`: `mem[[o₁] · o₂]` is the source selected by `mode`. -/
  | deref (o1 o2 o3 : K) (mode : DerefMode)
  /-- `JUMP [o_c, o_d, o_f]`: to `([o_d], [o_f])` when `[o_c] ≠ 0`, else fall through. -/
  | jump (oc od of : K)
  /-- `BLAKE2S [o_{m₀}, …, o_{m₃}, o_cv, o_out, o_md]`: the compression of the four message
  cells under the chaining-value pair at `o_cv`, into the pair at `o_out`, with metadata
  `[o_md]`. -/
  | blake2s (om : Fin 4 → K) (ocv oout omd : K)
  deriving DecidableEq

/-- The opcode of an instruction. -/
def Instr.opcode : Instr → Opcode
  | .xor .. => .xor
  | .mulNative .. => .mulNative
  | .setConstant .. => .setConstant
  | .deref .. => .deref
  | .jump .. => .jump
  | .blake2s .. => .blake2s

/-! ## Programs -/

/-- A bytecode of `2 ^ logSize` instructions within the verifier's cap (specification §6.4;
`cpu/mod.rs:158-159`); instruction `i` sits at address `g ^ i`. -/
structure Program where
  /-- The bytecode log-size `κ_bc`. -/
  logSize : ℕ
  /-- The cap `κ_bc ≤ 32`. -/
  logSize_le : logSize ≤ maxLogBytecode
  /-- The instructions, by logical index. -/
  code : Fin (2 ^ logSize) → Instr

/-- Fetch the instruction at `pc`: `some (code i)` when `pc = g ^ i`, `none` otherwise
(specification §2, execution loop step 1). -/
noncomputable def Program.fetch (prog : Program) (pc : K) : Option Instr :=
  (gLog? prog.logSize pc).map prog.code

/-! ## Proof helpers -/

/-- The cap keeps the bytecode inside the address space `gLog?_spec` covers. -/
private theorem Program.logSize_lt (prog : Program) : prog.logSize < 64 :=
  lt_of_le_of_lt prog.logSize_le (by decide)

/-! ## Load-bearing lemmas -/

/-- Fetching at the address of index `i` gives instruction `i`. -/
theorem Program.fetch_gpow (prog : Program) (i : Fin (2 ^ prog.logSize)) :
    prog.fetch (gpow i) = some (prog.code i) := by
  rw [Program.fetch, (gLog?_spec prog.logSize_lt).mpr rfl, Option.map_some]

/-- A successful fetch is the instruction of the counter's index. -/
theorem Program.fetch_eq_some_iff (prog : Program) {pc : K} {ins : Instr} :
    prog.fetch pc = some ins ↔ ∃ i : Fin (2 ^ prog.logSize), pc = gpow i ∧ prog.code i = ins := by
  simp only [Program.fetch, Option.map_eq_some_iff, gLog?_spec prog.logSize_lt]

/-- A fetch fails exactly at the counters that are no power below `2 ^ logSize`. -/
theorem Program.fetch_eq_none_iff (prog : Program) {pc : K} :
    prog.fetch pc = none ↔ ∀ i : Fin (2 ^ prog.logSize), pc ≠ gpow i := by
  rw [Program.fetch, Option.map_eq_none_iff, gLog?_eq_none_iff]

/-- Program counter `0` fetches nothing. -/
theorem Program.fetch_zero (prog : Program) : prog.fetch 0 = none := by
  rw [Program.fetch, gLog?_zero, Option.map_none]

end
end LeanerVM.Semantics
