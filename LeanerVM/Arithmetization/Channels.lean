/-
  LeanerVM.Arithmetization.Channels

  The three bus interactions of leanISA as three direction-tagged Clean channels, the image a
  channel guarantee is stated against, the two read gadgets, and the bus data of every channel.
-/

module

public import LeanerVM.Parameters.CleanField
public import LeanerVM.Semantics.Step
public import LeanerVM.Arithmetization.Bytecode
public import Clean.Circuit.Basic
public import Clean.Utils.Tactics.ProvableStructDeriving
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# The bus channels

leanISA roadmap Layer 5 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `9dd71e82`.

**The tuples** (Category B). Every bus tuple is sixteen `K` slots: a domain separator, then the
interaction's coordinates, then zeros (specification §5.1,
`doc/leanvm/body/05-arithmetization.tex:12` and `:16`; `crates/lean_vm/src/tables.rs:90-92`,
`SEP_STATE`, `SEP_MEM`, `SEP_BYTECODE`). The three interactions and their coordinate orders:

* state, separator `g^0`: `(pc, fp)` (§6.1, `06-bus-interactions.tex:8`; `tables.rs:127-141`);
* memory, separator `g^1`: `(addr, count, v₀, v₁, v₂)`, a read of the word `v` at `addr` with
  count `count` (§6.2 "Tuple and columns" and "Flush rules", `:40-47`, and §6.3, `:86`;
  `tables.rs:159-166`);
* bytecode, separator `g^2`: `(pc, count, opcode, op₁, …, op₇)`, the entry of Layer 4 after the
  address and the count (§6.4, `:90-92`; `tables.rs:145-152`).

A typed message is one such coordinate list: the state message is the register pair `Regs` of
Layer 3 itself, over `K` when evaluated and over `Expression K` in a row (one structure, one
meaning), and `MemMsg` and `BytecodeMsg` are the two lookup tuples. The three `toElements`
lemmas pin the order Clean flattens a message in to the specification's; `busTuple` is the
sixteen-slot form, and `channelSep` names each channel's separator as data, so that the
proof-system roadmap (issue #12) reads the M3 bus off these channels rather than transcribing the
tuples again (issue #13).

**The channels** (Category A: specification §6, Theorem 6.4 and Corollary 6.5). leanVM has exactly
three buses, one per separator, and so does the Lean: `StateChannel`, `MemChannel` and
`BytecodeChannel`. Every interaction carries Clean's direction tag (`ChannelDirection.push` or
`ChannelDirection.pull`), never read off the sign of a multiplicity, which carries none over `K`
(`-1 = 1`, acceptance test 13). A read is `pull (addr, count, v)` then `push (addr, g·count, v)`
on one channel (§6.2 "Flush rules"); the lookup theorem says that when the bus balances, every
count is nonzero, and there are fewer than `2^64 - 1` reads, every pulled memory tuple is a
correct read of the committed image and every pulled bytecode tuple is an entry of the public
program. What a pull of multiplicity `1` may assume locally is the channel's `Guarantees`, and
what an active push owes is the same proposition (Clean's `ChannelDirection.Requirements`):
`MemChannel` states the whole lookup fact, `MemImage.read` of the image named by the prover
data, since the image is committed and lives nowhere else; `BytecodeChannel` states only that the
entry decodes, through Layer 4's `decode`, to an instruction, a static fact about the tuple that
names no program (the paragraph on the program below), which is all a table needs (`DEREF`'s flag
pair must be a store mode's) and which Layer 9 derives from the lookup theorem together with the
strong fact, that the entry is the program's at the pulled counter. A read's push re-sends the
pulled address and word, so a table discharges what its pushes owe from what its pulls are
granted. The state channel carries no guarantee: a pulled state need not be reachable, since the
fill blocks of §8.3 are closed walks disjoint from the run, and what the state channel yields is
the walk decomposition of Layer 9 (roadmap acceptance test 21, issue #10). Balance is Clean's
multiset balance (Layer 8).

**The image** is read off Clean's `ProverData`, the string-keyed store a component's `Spec`
sees. Its `"mem"` table is the memory block's input rows (`MemRow`), derived by Clean from the
committed block (`Air.Flat.deriveProverData`), so `memRows` reads the value columns of the block.
`imageOf` is total, since a channel guarantee is a total proposition on arbitrary data, and so it
normalises: it takes the *floor* logarithm of the table's row count, capped at the verifier's
bound (`maxLogMem`), as its log-size, which drops the rows at indices from that power of two on
whenever the count is not exactly it. The cap also keeps `κ < 64`, the hypothesis under which
`MemImage.read` reads an address as an index (`gLog?_spec`), so `MemChannel.Guarantees` means
what it says on every data. In a witness the block has exactly `2^κ` rows, `κ` the announced
log-size (Layer 8), so nothing is dropped there (`imageOf_fst`).

**The program is public and the channels are program-free.** leanVM's bytecode is "public,
i.e. not committed, the verifier can evaluate it directly" (§6.4, `06-bus-interactions.tex:93`):
the eight entry columns ride the bytecode block as `Coord::Public` (`cpu/layout.rs:8-11`,
`:288-290`, `:383-395`; `leaf.rs:36-39`), and every opcode table's read is its own constant opcode
and its own operand columns, `[Const(BC), Col(pc), Col(count), Const(opcode), operands…]`
(`tables.rs:143-152`): no table knows the program, and what binds a row's operands to the program
is the bus, Theorem 6.4 applied to the bytecode channel. The Lean follows that division of
labour. No guarantee reads the program off the prover data: a program read off data the prover
supplies would be one the prover chose (acceptance test 22, status finding F10); the derived
data's `"bytecode"` rows are the block's fixed columns, but nothing here reads them. Nor is the
program a parameter of the channels or of the tables (status decision 14). It enters as the
fixed columns of the bytecode block (Layer 7) and as the verifier's sentinel counter.

## Wrong readings excluded

* The direction of an interaction is its tag, never its multiplicity: over `K`, `-1 = 1`.
* `Channel.emit` pushes at an arbitrary multiplicity; `memRead` and `bytecodeRead` use
  `Channel.pull` and `Channel.push`, whose multiplicity is `1`.
* The element order of a typed message is its field order, a vector field contributing its
  elements in place: `(addr, count, v₀, v₁, v₂)`, never `(v, addr, count)` or the separator
  inside the message (`memMsg_toElements`).
* A table whose row count is not a power of two within its cap is silently truncated by
  `imageOf` (a three-row store yields a one-bit image, tests); the empty store's image still has
  one word.
* The bytecode guarantee is not `True`: `DEREF`'s constraints are defined at the flag pair
  `(1, 1)`, which is no store mode's (`tables.rs:616-623`), so its soundness needs the pulled
  entry to decode; that every entry on the bus does is a fact about the public program
  (`decode_entry` on the block's fixed columns), and Layer 9 derives it (tests: the pair `(1, 1)`
  is rejected at every counter, acceptance test 18).
* The bytecode guarantee names no program: neither one read off the prover data, which the
  prover chooses (status finding F10), nor a parameter, which would put the program into every
  table's type (decision 14). `BytecodeChannel.Guarantees` is the same proposition on every data
  (tests, `Iff.rfl`).
-/

namespace LeanerVM.Semantics

/-! ## The state message -/

-- The state message is the register pair of Layer 3: `Regs K` evaluated, `Regs (Expression K)`
-- in a row (specification §6.1). Derived in the structure's own namespace, where Clean's handler
-- names its helpers after the structure.
deriving instance ProvableStruct for Regs

end LeanerVM.Semantics

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

/-! ## Messages -/

/-- The direction of a bus interaction, Clean's tag (`.push` or `.pull`); the one place leanerVM
names Clean's type. -/
abbrev BusDir : Type := ChannelDirection

/-- The memory tuple after its separator: `(addr, count, v₀, v₁, v₂)`, a read of the word
`v = v₀ + v₁·y + v₂·y²` at address `addr` with count `count` (specification §6.2, §6.3). -/
structure MemMsg (F : Type) where
  /-- The address, `fp · o` for an operand `o`. -/
  addr : F
  /-- The read count, a power of `g`. -/
  count : F
  /-- The three limbs of the word. -/
  v : Vector F 3
  deriving ProvableStruct

/-- The bytecode tuple after its separator: `(pc, count, opcode, op₁, …, op₇)`, a read of the
entry `(opcode, op₁, …, op₇)` of Layer 4 at counter `pc` (specification §6.4). -/
structure BytecodeMsg (F : Type) where
  /-- The program counter, the entry's address. -/
  pc : F
  /-- The read count. -/
  count : F
  /-- The opcode, coordinate 3 of the tuple. -/
  opcode : F
  /-- The seven operand slots. -/
  op : Vector F 7
  deriving ProvableStruct

/-! ## The image in the prover data -/

/-- A row of the memory block: the address `g^i` (the index column of §6.5, a fixed column), the
finalize count `g^(A[i])` (`MFCNT`), and the word's three limbs (`MEM_LO, MEM_HI, MEM_TOP`;
`layout.rs:13-16`). Its rows are the `"mem"` table of the prover data. -/
structure MemRow (F : Type) where
  /-- The address, `g^i` for row `i`. -/
  idx : F
  /-- The finalize count, `g^(A[i])` for an address read `A[i]` times. -/
  cntFin : F
  /-- The word at the address, as limbs. -/
  m : Vector F 3
  deriving ProvableStruct

/-- The prover-data table holding the memory image: the memory block's name, under which Clean
derives the block's input rows. The program has no table: it is public (the module docstring). -/
def memDataName : String := "mem"

/-- The words of the `"mem"` table: the value columns of the memory block's rows. -/
def memRows (data : ProverData K) : Array (Vector K 3) :=
  (data.getRows memDataName MemRow).map (·.m)

/-- The memory image named by the prover data: `κ` is the floor logarithm of the `"mem"` row
count, capped at `maxLogMem`, word `i` is row `i` as limbs `(c₀, c₁, c₂)`, and a missing row
reads as `0`. Rows at indices from `2^κ` on are dropped; in a witness there are none
(`imageOf_fst`). -/
def imageOf (data : ProverData K) : (κ : ℕ) × MemImage κ :=
  ⟨min (Nat.log 2 (memRows data).size) maxLogMem,
    fun i ↦ (((memRows data)[(i : ℕ)]?).map fun v ↦ E.ofLimbs v[0] v[1] v[2]).getD 0⟩

/-! ## The three channels -/

/-- The state channel, separator `g^0`. No guarantee: a pulled state need not be reachable
(acceptance test 21). -/
def StateChannel : Channel K Regs where
  name := "state"
  Guarantees _ _ := True

/-- The memory channel, separator `g^1`: a pulled tuple is a correct read of the image named by
the prover data (specification Theorem 6.4 and Corollary 6.5), and a push owes it. -/
def MemChannel : Channel K MemMsg where
  name := "memory"
  Guarantees m data := (imageOf data).2.read m.addr = some (E.ofLimbs m.v[0] m.v[1] m.v[2])

/-- The bytecode channel, separator `g^2`: the entry decodes to an instruction (Layer 4). A
static fact about the tuple alone, naming no program and reading no data: it is what the `DEREF`
table needs (a flag pair that is no store mode decodes to nothing) and what every entry of the
public program satisfies (`decode_entry`). That the entry is the program's at the pulled counter
is Layer 9's, specification Theorem 6.4 on the bytecode channel from the block's fixed columns;
the module docstring says why neither a program read off the data nor a program parameter
belongs here. -/
def BytecodeChannel : Channel K BytecodeMsg where
  name := "bytecode"
  Guarantees b _ := ∃ ins, decode (#v[b.opcode] ++ b.op) = some ins

/-! ## The read gadgets -/

/-- A memory read of the word `v` at `addr` with count `count`: pull `(addr, count, v)`, push
`(addr, g·count, v)` (specification §6.2 "Flush rules"; `tables.rs:159-166`). The pull is granted
`MemChannel.Guarantees`, which the push, carrying the same address and word, owes. -/
def memRead (addr count : Expression K) (v : Vector (Expression K) 3) : Circuit K Unit := do
  MemChannel.pull ⟨addr, count, v⟩
  MemChannel.push ⟨addr, Expression.const g * count, v⟩

/-- A bytecode read of the entry `(opcode, op)` at counter `pc` with count `count`: pull
`(pc, count, opcode, op)`, push `(pc, g·count, opcode, op)` (specification §6.2, §6.4;
`tables.rs:145-152`). -/
def bytecodeRead (pc count opcode : Expression K) (op : Vector (Expression K) 7) :
    Circuit K Unit := do
  BytecodeChannel.pull ⟨pc, count, opcode, op⟩
  BytecodeChannel.push ⟨pc, Expression.const g * count, opcode, op⟩

/-! ## Bus data -/

/-- The domain separator of a channel (specification §5.1 "Domain separation";
`tables.rs:90-92`): `g^0` for the state channel, `g^1` for memory, `g^2` for bytecode, and `0`,
which is no separator, for any other channel. -/
def channelSep (c : RawChannel K) : K :=
  if c.name = StateChannel.name then gpow 0
  else if c.name = MemChannel.name then gpow 1
  else if c.name = BytecodeChannel.name then gpow 2
  else 0

/-- The sixteen-slot bus tuple of a message on a channel: the channel's separator, then the
message's elements in order, then zeros (specification §5.1, `05-arithmetization.tex:12`). -/
def busTuple (c : RawChannel K) (msg : List K) : Vector K 16 :=
  let m := fun j : ℕ ↦ msg.getD j 0
  #v[channelSep c, m 0, m 1, m 2, m 3, m 4, m 5, m 6, m 7, m 8, m 9, m 10, m 11, m 12, m 13,
    m 14]

/-! ## Load-bearing lemmas -/

/-- A state message flattens to `[pc, fp]` (specification §6.1). -/
theorem regs_toElements (s : Regs K) : (toElements s).toList = [s.pc, s.fp] := by
  obtain ⟨pc, fp⟩ := s
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]

/-- A memory message flattens to `[addr, count, v₀, v₁, v₂]` (specification §6.2). -/
theorem memMsg_toElements (m : MemMsg K) :
    (toElements m).toList = [m.addr, m.count] ++ m.v.toList := by
  obtain ⟨addr, count, v⟩ := m
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]

/-- A bytecode message flattens to `[pc, count, opcode, op₁, …, op₇]` (specification §6.4). -/
theorem bytecodeMsg_toElements (b : BytecodeMsg K) :
    (toElements b).toList = [b.pc, b.count, b.opcode] ++ b.op.toList := by
  obtain ⟨pc, count, opcode, op⟩ := b
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]

/-- Slot `0` of a bus tuple is the separator and slot `j + 1` is element `j` of the message,
`0` past its end. -/
theorem busTuple_getElem (c : RawChannel K) (msg : List K) (j : ℕ) (hj : j < 16) :
    (busTuple c msg)[j] = if j = 0 then channelSep c else msg.getD (j - 1) 0 := by
  interval_cases j <;> simp [busTuple]

/-- When the `"mem"` table has `2^κ` rows within the cap, the image's log-size is `κ`: nothing
is dropped. -/
theorem imageOf_fst {data : ProverData K} {κ : ℕ} (hκ : κ ≤ maxLogMem)
    (h : (memRows data).size = 2 ^ κ) : (imageOf data).1 = κ := by
  show min (Nat.log 2 (memRows data).size) maxLogMem = κ
  rw [h, Nat.log_pow (by norm_num), Nat.min_eq_left hκ]

/-- Word `i` of the image is row `i` of the `"mem"` table, as limbs, read through `getElem?`
(a bounded `getElem` on a `2^κ`-row table makes both the elaborator and the kernel unroll it,
status finding E8). -/
theorem imageOf_apply {data : ProverData K} (i : Fin (2 ^ (imageOf data).1)) {v : Vector K 3}
    (hv : (memRows data)[(i : ℕ)]? = some v) :
    (imageOf data).2 i = E.ofLimbs v[0] v[1] v[2] := by
  show (((memRows data)[(i : ℕ)]?).map fun v ↦ E.ofLimbs v[0] v[1] v[2]).getD 0 = _
  rw [hv]
  rfl

/-- The image's log-size is below `64`, the range `MemImage.read` reads addresses in. -/
theorem imageOf_fst_lt (data : ProverData K) : (imageOf data).1 < 64 :=
  lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)

end LeanerVM.Arithmetization
