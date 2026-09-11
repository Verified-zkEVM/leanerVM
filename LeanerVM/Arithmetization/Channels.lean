/-
  LeanerVM.Arithmetization.Channels

  The three bus interactions of leanISA as six Clean channels, the image and program a channel
  guarantee is stated against, the two read gadgets, and the bus data of every channel.
  A plain (non-`module`) file: it imports Clean, which is not a `module` at `93c9d1ef`.
-/

import LeanerVM.Parameters.CleanField
import LeanerVM.Semantics.Step
import LeanerVM.Arithmetization.Bytecode
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableStructDeriving
import Mathlib.Data.Nat.Log

/-!
# The bus channels

leanISA roadmap Layer 5 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `93c9d1ef`.

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
sixteen-slot form, and `channelSep` and `channelDir` name each channel's separator and
direction as data, so that the proof-system roadmap (issue #12) reads the M3 bus off these
channels rather than transcribing the tuples again (issue #13).

**The channels** (Category A: specification §6, Theorem 6.4 and Corollary 6.5). A read is
`pull (addr, count, v)` and `push (addr, g·count, v)` (§6.2 "Flush rules"); the lookup theorem
says that when the bus balances, every count is nonzero, and there are fewer than `2^64 - 1`
reads, every pulled memory tuple is a correct read of the committed image and every pulled
bytecode tuple is an entry of the public program. That per-tuple fact is what a pull may assume
and is the channel's `Guarantees`: `MemPull` states it as `MemImage.read` of the image named by
the prover data, `BytecodePull` as `Program.fetch` of the program named by the prover data
against Layer 4's `decode`. The state pull carries no guarantee: a pulled state need not be
reachable, since the fill blocks of §8.3 are closed walks disjoint from the run, and what the
state channel yields is the walk decomposition of Layer 9 (roadmap acceptance test 21, issue
#10). Pushes carry no guarantee; what a push must satisfy is the emitting component's `Spec`.

**Direction as data.** Clean's `Channel.toRaw` reads the direction of an interaction off the sign
of its multiplicity: a pull is `-1` and is granted the guarantee, and a push must satisfy the
channel's `Requirements` when its multiplicity is neither `-1` nor `0`. In `K`, `-1 = 1`, so that
reading makes every requirement vacuous and grants the guarantee at the multiplicity of a push
(roadmap acceptance test 13; the tests exhibit both). Each interaction is therefore a *pair* of
channels, `*.pull` and `*.push`, and the direction of an interaction is the channel it is on:
`memRead` and `bytecodeRead` emit through `Channel.pull` on the pull channel, the one emitter
whose interaction a soundness proof may assume the guarantee of (it sets `assumeGuarantees`
and multiplicity `-1`, which evaluates to `1`), and through `Channel.push` on the push channel
(multiplicity `1`, nothing assumed). Every interaction of Layers 6 and 7 thus has multiplicity
`1`; balance is the multiset equality of the two channels of a pair (Layer 8, `BalancedPair`),
never Clean's field-sum `BalancedInteractions`, which admits at most one interaction over `K`
(acceptance test 14). The roadmap's dependency table states the Clean change that turns both
workarounds into deletions; `Direction` and `channelDir` are deleted in favour of Clean's
direction tag when that change is upstreamed (issue #16).

**The image and the program** are read off Clean's `ProverData`, the string-keyed store a
component's `Spec` sees: `memRows` is its `"mem"` table, one row of three limbs per word, and
`bytecodeRows` its `"bytecode"` table, one eight-coordinate entry per instruction. `imageOf` and
`programOf` are total, since a channel guarantee is a total proposition on arbitrary data, and
so they normalise: each takes the *floor* logarithm of its table's row count as the log-size,
which drops the rows at indices from `2^κ` on when the count is not a power of two, and
`programOf` further caps the log-size at `maxLogBytecode`. `WellShapedData` is the shape under
which neither drops anything (each table's row count is exactly a power of two, the bytecode's
within the cap), and `imageOf_apply` and `programOf_code` are the two specifications under it;
it is a conjunct of Layer 8's `Caps`, the verifier's check of the announced sizes, never a new
hypothesis on a theorem. Layer 8's hypotheses `SeedRowsAreTheImage` and
`BytecodeRowsAreTheProgram` tie the two tables to the committed seed rows and the public program
until Clean PR #446 supplies proof-committed data (roadmap dependency table).

## Wrong readings excluded

* A push on a pull channel is not a push: `memRead` never emits on `MemPull` with `push`, and a
  `pull` on a push channel is granted `True`. The direction is `channelDir`, read from the channel
  (acceptance test 13).
* `-1 = 1` in `K`: a multiplicity carries no direction, and Clean's `Requirements` hold of every
  interaction a component emits (tests).
* `Channel.emit`, the roadmap sketch's emitter, sets `assumeGuarantees := false`, so a soundness
  proof of a component using it could never assume the guarantee of its own pull; `memRead` and
  `bytecodeRead` use `Channel.pull` instead.
* The element order of a typed message is its field order, a vector field contributing its
  elements in place: `(addr, count, v₀, v₁, v₂)`, never `(v, addr, count)` or the separator
  inside the message (`memMsg_toElements`).
* A table whose row count is not a power of two is silently truncated by `imageOf` and
  `programOf` (a three-row store yields a one-bit image, tests) and is not `WellShapedData`;
  the empty store is not either, since its image still has one word.
* A `"bytecode"` row that decodes to nothing is `XOR 0 0 0`, whose first read is at address `0`
  and fails (acceptance test 2), so `step` executes nothing there; `BytecodeRowsAreTheProgram`
  excludes such rows anyway.
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

/-! ## The image and the program in the prover data -/

/-- The prover-data table holding the memory image: one row of three limbs per word. -/
def memDataName : String := "mem"

/-- The prover-data table holding the program: one eight-coordinate entry per instruction. -/
def bytecodeDataName : String := "bytecode"

/-- The rows of the `"mem"` table. -/
def memRows (data : ProverData K) : Array (Vector K 3) := data memDataName 3

/-- The rows of the `"bytecode"` table. -/
def bytecodeRows (data : ProverData K) : Array (Vector K 8) := data bytecodeDataName 8

/-- The memory image named by the prover data: `κ` is the floor logarithm of the `"mem"` row
count, word `i` is row `i` as limbs `(c₀, c₁, c₂)`, and a missing row reads as `0`. Rows at
indices from `2^κ` on are dropped; `WellShapedData` is the shape under which there are none. -/
def imageOf (data : ProverData K) : (κ : ℕ) × MemImage κ :=
  ⟨Nat.log 2 (memRows data).size,
    fun i ↦ (((memRows data)[(i : ℕ)]?).map fun v ↦ E.ofLimbs v[0] v[1] v[2]).getD 0⟩

/-- The program named by the prover data: `logSize` is the floor logarithm of the `"bytecode"`
row count, capped at `maxLogBytecode`, and instruction `i` is row `i` decoded; a missing row, or
one that is no instruction's entry, is `XOR 0 0 0`, whose first read fails. Rows at indices from
`2^logSize` on are dropped; `WellShapedData` is the shape under which there are none. -/
def programOf (data : ProverData K) : Program where
  logSize := min (Nat.log 2 (bytecodeRows data).size) maxLogBytecode
  logSize_le := Nat.min_le_right _ _
  code i := ((bytecodeRows data)[(i : ℕ)]? >>= decode).getD (.xor 0 0 0)

/-- The prover data is well shaped: the `"mem"` table has exactly the `2^κ` rows of its image
and the `"bytecode"` table exactly the `2^logSize` entries of its program, that is, each row
count is a power of two and the bytecode's is at most `2^maxLogBytecode`
(`wellShapedData_iff`), so that `imageOf` and `programOf` drop nothing. A conjunct of Layer 8's
`Caps`. -/
structure WellShapedData (data : ProverData K) : Prop where
  /-- The `"mem"` table has `2^κ` rows. -/
  memRows_size : (memRows data).size = 2 ^ (imageOf data).1
  /-- The `"bytecode"` table has `2^logSize` rows. -/
  bytecodeRows_size : (bytecodeRows data).size = 2 ^ (programOf data).logSize

/-! ## The six channels -/

/-- The state pull, separator `g^0`. No guarantee: a pulled state need not be reachable
(acceptance test 21). -/
def StatePull : Channel K Regs where
  name := "st.pull"
  Guarantees _ _ := True

/-- The state push, separator `g^0`. -/
def StatePush : Channel K Regs where
  name := "st.push"
  Guarantees _ _ := True

/-- The memory pull, separator `g^1`: a pulled tuple is a correct read of the image named by
the prover data (specification Theorem 6.4 and Corollary 6.5). -/
def MemPull : Channel K MemMsg where
  name := "mem.pull"
  Guarantees m data := (imageOf data).2.read m.addr = some (E.ofLimbs m.v[0] m.v[1] m.v[2])

/-- The memory push, separator `g^1`. -/
def MemPush : Channel K MemMsg where
  name := "mem.push"
  Guarantees _ _ := True

/-- The bytecode pull, separator `g^2`: fetching at the pulled counter from the program named
by the prover data is decoding the pulled entry (specification Theorem 6.4; Layer 4). -/
def BytecodePull : Channel K BytecodeMsg where
  name := "bc.pull"
  Guarantees b data := (programOf data).fetch b.pc = decode (#v[b.opcode] ++ b.op)

/-- The bytecode push, separator `g^2`. -/
def BytecodePush : Channel K BytecodeMsg where
  name := "bc.push"
  Guarantees _ _ := True

/-! ## The read gadgets -/

/-- A memory read of the word `v` at `addr` with count `count`: pull `(addr, count, v)`, push
`(addr, g·count, v)` (specification §6.2 "Flush rules"; `tables.rs:159-166`). The pull is a
`Channel.pull`, so that a soundness proof may assume `MemPull.Guarantees` of it. -/
def memRead (addr count : Expression K) (v : Vector (Expression K) 3) : Circuit K Unit := do
  MemPull.pull ⟨addr, count, v⟩
  MemPush.push ⟨addr, Expression.const g * count, v⟩

/-- A bytecode read of the entry `(opcode, op)` at counter `pc` with count `count`: pull
`(pc, count, opcode, op)`, push `(pc, g·count, opcode, op)` (specification §6.2, §6.4;
`tables.rs:145-152`). -/
def bytecodeRead (pc count opcode : Expression K) (op : Vector (Expression K) 7) :
    Circuit K Unit := do
  BytecodePull.pull ⟨pc, count, opcode, op⟩
  BytecodePush.push ⟨pc, Expression.const g * count, opcode, op⟩

/-! ## Bus data -/

/-- The direction of a bus flush (specification §5.1 "The bus"). Clean at `93c9d1ef` has no such
type, only the sign of a multiplicity, which carries no information over `K`; this one and
`channelDir` are deleted in favour of Clean's direction tag once that change is upstreamed
(issue #16, the roadmap's dependency table). -/
inductive Direction
  | pull
  | push
  deriving DecidableEq, Repr

/-- The direction of a channel, read from its name: the three `*.pull` channels pull, every other
channel pushes. Never the sign of a multiplicity (acceptance test 13). Deleted with `Direction`
once Clean tags interactions with their direction (issue #16). -/
def channelDir (c : RawChannel K) : Direction :=
  if c.name = StatePull.name ∨ c.name = MemPull.name ∨ c.name = BytecodePull.name then .pull
  else .push

/-- The domain separator of a channel (specification §5.1 "Domain separation";
`tables.rs:90-92`): `g^0` for the state pair, `g^1` for memory, `g^2` for bytecode, and `0`,
which is no separator, for any other channel. -/
def channelSep (c : RawChannel K) : K :=
  if c.name = StatePull.name ∨ c.name = StatePush.name then gpow 0
  else if c.name = MemPull.name ∨ c.name = MemPush.name then gpow 1
  else if c.name = BytecodePull.name ∨ c.name = BytecodePush.name then gpow 2
  else 0

/-- The sixteen-slot bus tuple of a message on a channel: the channel's separator, then the
message's elements in order, then zeros (specification §5.1, `05-arithmetization.tex:12`). -/
def busTuple (c : RawChannel K) (msg : List K) : Vector K 16 :=
  let m := fun j : ℕ ↦ msg.getD j 0
  #v[channelSep c, m 0, m 1, m 2, m 3, m 4, m 5, m 6, m 7, m 8, m 9, m 10, m 11, m 12, m 13,
    m 14]

/-! ## Load-bearing lemmas -/

/-- A state message flattens to `[pc, fp]` (specification §6.1). -/
theorem regs_toElements (s : Regs K) : (toElements s).toList = [s.pc, s.fp] := rfl

/-- A memory message flattens to `[addr, count, v₀, v₁, v₂]` (specification §6.2). -/
theorem memMsg_toElements (m : MemMsg K) :
    (toElements m).toList = [m.addr, m.count] ++ m.v.toList := by
  obtain ⟨addr, count, v⟩ := m
  change (Vector.cast _ (#v[addr] ++ (#v[count] ++ (v ++ #v[])))).toList = _
  rw [Vector.toList_cast, Vector.toList_append, Vector.toList_append, Vector.toList_append]
  simp

/-- A bytecode message flattens to `[pc, count, opcode, op₁, …, op₇]` (specification §6.4). -/
theorem bytecodeMsg_toElements (b : BytecodeMsg K) :
    (toElements b).toList = [b.pc, b.count, b.opcode] ++ b.op.toList := by
  obtain ⟨pc, count, opcode, op⟩ := b
  change (Vector.cast _ (#v[pc] ++ (#v[count] ++ (#v[opcode] ++ (op ++ #v[]))))).toList = _
  rw [Vector.toList_cast, Vector.toList_append, Vector.toList_append, Vector.toList_append,
    Vector.toList_append]
  simp

/-- Slot `0` of a bus tuple is the separator and slot `j + 1` is element `j` of the message,
`0` past its end. -/
theorem busTuple_getElem (c : RawChannel K) (msg : List K) (j : ℕ) (hj : j < 16) :
    (busTuple c msg)[j] = if j = 0 then channelSep c else msg.getD (j - 1) 0 := by
  interval_cases j <;> simp [busTuple]

/-- Well shaped means: each table's row count is a power of two, the bytecode's at most
`2^maxLogBytecode`. -/
theorem wellShapedData_iff (data : ProverData K) :
    WellShapedData data ↔
      (∃ κ, (memRows data).size = 2 ^ κ) ∧
        ∃ k ≤ maxLogBytecode, (bytecodeRows data).size = 2 ^ k := by
  constructor
  · rintro ⟨hm, hb⟩
    exact ⟨⟨_, hm⟩, _, Nat.min_le_right _ _, hb⟩
  · rintro ⟨⟨κ, hκ⟩, k, hk, hkb⟩
    refine ⟨?_, ?_⟩
    · show (memRows data).size = 2 ^ Nat.log 2 (memRows data).size
      rw [hκ, Nat.log_pow (by norm_num)]
    · show (bytecodeRows data).size = 2 ^ min (Nat.log 2 (bytecodeRows data).size) maxLogBytecode
      rw [hkb, Nat.log_pow (by norm_num), Nat.min_eq_left hk]

/-- Under the shape, every index of the image is a row of the `"mem"` table. -/
theorem WellShapedData.memIndex_lt {data : ProverData K} (h : WellShapedData data)
    (i : Fin (2 ^ (imageOf data).1)) : (i : ℕ) < (memRows data).size := by
  rw [h.memRows_size]; exact i.isLt

/-- Under the shape, every index of the program is a row of the `"bytecode"` table. -/
theorem WellShapedData.bytecodeIndex_lt {data : ProverData K} (h : WellShapedData data)
    (i : Fin (2 ^ (programOf data).logSize)) : (i : ℕ) < (bytecodeRows data).size := by
  rw [h.bytecodeRows_size]; exact i.isLt

/-- Under the shape, word `i` of the image is row `i` of the `"mem"` table, as limbs. -/
theorem imageOf_apply {data : ProverData K} (h : WellShapedData data)
    (i : Fin (2 ^ (imageOf data).1)) {v : Vector K 3}
    (hv : (memRows data)[(i : ℕ)]'(h.memIndex_lt i) = v) :
    (imageOf data).2 i = E.ofLimbs v[0] v[1] v[2] := by
  simp [imageOf, Array.getElem?_eq_getElem (h.memIndex_lt i), hv]

/-- Under the shape, instruction `i` of the program is row `i` of the `"bytecode"` table,
decoded. -/
theorem programOf_code {data : ProverData K} (h : WellShapedData data)
    (i : Fin (2 ^ (programOf data).logSize)) {ins : Instr}
    (hd : decode ((bytecodeRows data)[(i : ℕ)]'(h.bytecodeIndex_lt i)) = some ins) :
    (programOf data).code i = ins := by
  simp [programOf, Array.getElem?_eq_getElem (h.bytecodeIndex_lt i), hd]

end LeanerVM.Arithmetization
