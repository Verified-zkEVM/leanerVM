/-
  LeanerVM.Arithmetization.Channels

  The three bus interactions of leanISA as six Clean channels, the image and program a channel
  guarantee is stated against, the two read gadgets, and the bus data of every channel.
  A plain (non-`module`) file: it imports Clean, which is not a `module` at `93c9d1ef`.
-/

import LeanerVM.Parameters.CleanField
import LeanerVM.Arithmetization.Bytecode
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableStructDeriving
import Mathlib.Data.Nat.Log

/-!
# The bus channels

leanISA roadmap Layer 5 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `93c9d1ef`.

**The tuples** (Category B). Every bus tuple is sixteen `K` slots: a domain separator, then the
interaction's coordinates, then zeros (specification §5.1, `doc/leanvm/body/05-arithmetization.tex:12`
and `:16`; `crates/lean_vm/src/tables.rs:90-92`, `SEP_STATE`, `SEP_MEM`, `SEP_BYTECODE`). The three
interactions and their coordinate orders:

* state, separator `g^0`: `(pc, fp)` (§6.1, `06-bus-interactions.tex:8`; `tables.rs:127-141`);
* memory, separator `g^1`: `(addr, count, v₀, v₁, v₂)`, a read of the word `v` at `addr` with
  count `count` (§6.2 "Tuple and columns" and "Flush rules", `:40-47`, and §6.3, `:86`;
  `tables.rs:159-166`);
* bytecode, separator `g^2`: `(pc, count, opcode, op₁, …, op₇)`, the entry of Layer 4 after the
  address and the count (§6.4, `:90-92`; `tables.rs:145-152`).

A typed message (`StateMsg`, `MemMsg`, `BytecodeMsg`) is one such coordinate list, and the three
`toElements` lemmas pin the order Clean flattens it in to the specification's; `busTuple` is the
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
workarounds into deletions.

**The image and the program** are read off Clean's `ProverData`, the string-keyed store a
component's `Spec` sees: `imageOf` takes the `"mem"` table, one row of three limbs per word, and
`programOf` the `"bytecode"` table, one eight-coordinate entry per instruction, each of log-size
the floor logarithm of its row count. Layer 8's hypotheses `SeedRowsAreTheImage` and
`BytecodeRowsAreTheProgram` tie them to the committed seed rows and the public program until
Clean PR #446 supplies proof-committed data (roadmap dependency table).

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
* A `"bytecode"` row that decodes to nothing is `XOR 0 0 0`, whose first read is at address `0`
  and fails (acceptance test 2), so `step` executes nothing there; `BytecodeRowsAreTheProgram`
  excludes such rows anyway.
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

/-! ## Messages -/

/-- The state tuple after its separator: `(pc, fp)` (specification §6.1). -/
structure StateMsg (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  deriving ProvableStruct

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

/-- The memory image named by the prover data: `κ` is the floor logarithm of the `"mem"` row
count, word `i` is row `i` as limbs `(c₀, c₁, c₂)`, and a missing row reads as `0`. -/
def imageOf (data : ProverData K) : (κ : ℕ) × MemImage κ :=
  let rows := data memDataName 3
  ⟨Nat.log 2 rows.size, fun i ↦ ((rows[(i : ℕ)]?).map fun v ↦ E.ofLimbs v[0] v[1] v[2]).getD 0⟩

/-- The program named by the prover data: `logSize` is the floor logarithm of the `"bytecode"`
row count, capped at `maxLogBytecode`, and instruction `i` is row `i` decoded; a missing row, or
one that is no instruction's entry, is `XOR 0 0 0`, whose first read fails. -/
def programOf (data : ProverData K) : Program where
  logSize := min (Nat.log 2 (data bytecodeDataName 8).size) maxLogBytecode
  logSize_le := Nat.min_le_right _ _
  code i := ((data bytecodeDataName 8)[(i : ℕ)]? >>= decode).getD (.xor 0 0 0)

/-! ## The six channels -/

/-- The state pull, separator `g^0`. No guarantee: a pulled state need not be reachable
(acceptance test 21). -/
def StatePull : Channel K StateMsg where
  name := "st.pull"
  Guarantees _ _ := True

/-- The state push, separator `g^0`. -/
def StatePush : Channel K StateMsg where
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

/-- The direction of a bus flush (specification §5.1 "The bus"). -/
inductive Direction
  | pull
  | push
  deriving DecidableEq, Repr

/-- The direction of a channel, read from its name: the three `*.pull` channels pull, every other
channel pushes. Never the sign of a multiplicity (acceptance test 13). -/
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
theorem stateMsg_toElements (s : StateMsg K) : (toElements s).toList = [s.pc, s.fp] := rfl

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

/-- Every index of the image is a row of the `"mem"` table once the table is nonempty. -/
theorem imageOf_index_lt (data : ProverData K) (i : Fin (2 ^ (imageOf data).1))
    (h : 0 < (data memDataName 3).size) : (i : ℕ) < (data memDataName 3).size :=
  lt_of_lt_of_le i.isLt (Nat.pow_log_le_self 2 h.ne')

/-- Word `i` of the image is row `i` of the `"mem"` table, as limbs. -/
theorem imageOf_apply (data : ProverData K) (i : Fin (2 ^ (imageOf data).1))
    (h : (i : ℕ) < (data memDataName 3).size) :
    (imageOf data).2 i =
      E.ofLimbs (data memDataName 3)[(i : ℕ)][0] (data memDataName 3)[(i : ℕ)][1]
        (data memDataName 3)[(i : ℕ)][2] := by
  simp [imageOf, Array.getElem?_eq_getElem h]

/-- Instruction `i` of the program is row `i` of the `"bytecode"` table, decoded. -/
theorem programOf_code (data : ProverData K) (i : Fin (2 ^ (programOf data).logSize))
    (h : (i : ℕ) < (data bytecodeDataName 8).size) {ins : Instr}
    (hd : decode (data bytecodeDataName 8)[(i : ℕ)] = some ins) :
    (programOf data).code i = ins := by
  simp [programOf, Array.getElem?_eq_getElem h, hd]

end LeanerVM.Arithmetization
