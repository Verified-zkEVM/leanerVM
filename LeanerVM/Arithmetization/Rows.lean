/-
  LeanerVM.Arithmetization.Rows

  What one row of each component of the leanISA ensemble sends on the bus, in closed form on
  arbitrary raw rows: the six opcode tables, the memory and bytecode blocks, and the verifier.
-/

module

public import LeanerVM.Arithmetization.Messages

@[expose] public section

/-!
# What a row sends

The messages one row of a component sends on each of the three channels in each direction, as
functions of the row's typed input `valueFromOffset Row 0 (t.environment row)`, Clean's
`Component.rowInput`: the first `size Row` cells of the raw row read as the typed row, a missing
cell `0`. The rows are arbitrary, honest or not, and nothing about the constraints is assumed.
Category A: facts about this repository's circuits, which transcribe leanVM at pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` (specification §5.1 "The bus", §6, §7;
`crates/lean_vm/src/tables.rs`, `cpu/layout.rs:352-395`), over Clean `ce2eee63`.

**Opcode rows.** A row of each of the six opcode tables sends an `OpcodeSends`: it pulls its
state `pull`, pushes `push`, reads its bytecode tuple `bc`, and reads the memory tuples `mem`.
A read pulls its tuple and pushes it with the count multiplied by `g` (§6.2 "Flush rules"), so
the pushes on the two lookup channels are the pulls, `bump`ed. `SendsOpcode t row s` states
the messages of `s` on each channel and direction; `xorSends`, `mulSends`, `setSends`,
`derefSends`, `jumpSends` and `blake2sSends` are the tables' sends, and `xor_sendsOpcode` and
its five siblings say that every row of a table sends them. Per row: one state pull and push,
one bytecode read, and three memory reads (`XOR`, `MUL_NATIVE`, `DEREF`, `JUMP`), one
(`SET_CONSTANT`) or nine (`BLAKE2S`).

**Blocks and verifier.** A memory block row pushes its seed `(idx, 1, m)` and pulls its
finalize `(idx, cntFin, m)` on the memory channel, a bytecode block row likewise on the bytecode
channel (§6.2 "Seed" and "Finalize"), and the verifier pushes `(1, 1)` and pulls
`(g^(N_prog - 1), 1)` on the state channel (§6.1). Every other channel carries nothing from
them.

**The witness.** `messagesOn_eq_flatMap` reads the messages a witness sends on a channel in a
direction as the verifier's (`verifierMessagesOn`) and its rows', table by table, and
`exists_sendsOpcode` says every row of the six opcode tables sends some `OpcodeSends` with at
most nine memory reads. Every interaction of a witness has multiplicity `1`
(`interactions_mult_eq_one`), so none is dropped by Clean's `activeMessages`.

The proofs read each row circuit's closed form over a row variable `x` with `eval env x = r`
(`Arithmetization.Messages`) and specialize it at Clean's `varFromOffset`
(`eval_varFromOffset_valueFromOffset`), reading each interaction as its channel name, direction
and message.

**From rows to interactions.** `exists_interaction_of_mem_rowMessagesOn` reads a row's message
as one of its table's interactions, and `mem_messagesOn_of_mem_rowMessagesOn`,
`exists_interaction_of_mem_messagesOn` and `mem_messagesOn_of_mem_interactions` carry it to and
from the witness: what a soundness proof needs to apply a lookup theorem, stated over
`w.interactions`, to one row.

## Wrong readings excluded

* A row's messages are not its columns: the third read of an `XOR` row carries the limb-wise
  sum, the `MUL_NATIVE` row's the product, the `DEREF` row's the store coordinates of its
  flags; none is a column.
* A read pushes `(addr, g·count, v)`, the count multiplied by `g`, never incremented, and the
  separator is not in the message (`MemMsg.bump`).
* The `JUMP` row's successor reads its local indicator `b`, the raw cell after its columns
  and its inverse witness, never a column of the typed row (`jumpSends`).
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics
open Air.Flat (Component EnsembleWitness)

/-! ## Reads -/

/-- The tuple a memory read pushes: the pulled tuple with its count multiplied by `g`
(specification §6.2 "Flush rules"). -/
def MemMsg.bump (m : MemMsg K) : MemMsg K := { m with count := g * m.count }

/-- The tuple a bytecode read pushes: the pulled tuple with its count multiplied by `g`. -/
def BytecodeMsg.bump (m : BytecodeMsg K) : BytecodeMsg K := { m with count := g * m.count }

/-! ## What an opcode row sends -/

/-- What one row of an opcode table sends (specification §6, §7): it pulls the state `pull` and
pushes `push`, reads the bytecode tuple `bc`, and reads the memory tuples `mem`, in order. -/
structure OpcodeSends where
  /-- The state pulled. -/
  pull : Regs K
  /-- The state pushed. -/
  push : Regs K
  /-- The bytecode tuple read. -/
  bc : BytecodeMsg K
  /-- The memory tuples read, in order. -/
  mem : List (MemMsg K)

/-- The row `row` of the table `t` sends `s`: one state pull and one push, the bytecode read's
pull and push, and each memory read's pull and push, the pushes the pulls with their counts
multiplied by `g` (§6.2 "Flush rules"). -/
structure SendsOpcode (t : Air.Flat.Table K) (row : Array K) (s : OpcodeSends) : Prop where
  /-- The state pulled. -/
  state_pull : rowMessagesOn t row StateChannel.toRaw .pull = [#[s.pull.pc, s.pull.fp]]
  /-- The state pushed. -/
  state_push : rowMessagesOn t row StateChannel.toRaw .push = [#[s.push.pc, s.push.fp]]
  /-- The bytecode read's pull. -/
  bytecode_pull : rowMessagesOn t row BytecodeChannel.toRaw .pull = [(toElements s.bc).toArray]
  /-- The bytecode read's push. -/
  bytecode_push :
    rowMessagesOn t row BytecodeChannel.toRaw .push = [(toElements s.bc.bump).toArray]
  /-- The memory reads' pulls. -/
  mem_pull : rowMessagesOn t row MemChannel.toRaw .pull = s.mem.map fun m ↦ (toElements m).toArray
  /-- The memory reads' pushes. -/
  mem_push :
    rowMessagesOn t row MemChannel.toRaw .push = s.mem.map fun m ↦ (toElements m.bump).toArray

/-- What an `XOR` row sends (specification §7.1; `tables.rs:483-495`): the fall-through step,
the bytecode tuple `(XOR, o_A, o_B, o_C, 0, 0, 0, 0)` at `pc`, and three memory reads, the
third carrying the limb-wise sum. -/
def xorSends (r : XorRow K) : OpcodeSends where
  pull := ⟨r.pc, r.fp⟩
  push := ⟨g * r.pc, r.fp⟩
  bc := ⟨r.pc, r.rbc, Opcode.xor.code, #v[r.oA, r.oB, r.oC, 0, 0, 0, 0]⟩
  mem := [⟨r.fp * r.oA, r.rA, r.vA⟩, ⟨r.fp * r.oB, r.rB, r.vB⟩,
    ⟨r.fp * r.oC, r.rC, #v[r.vA[0] + r.vB[0], r.vA[1] + r.vB[1], r.vA[2] + r.vB[2]]⟩]

/-- What a `MUL_NATIVE` row sends (specification §7.2): as `XOR`, with the third read carrying
the product's limbs (`TOWER_LANES`, `tables.rs:45-49`). -/
def mulSends (r : MulRow K) : OpcodeSends where
  pull := ⟨r.pc, r.fp⟩
  push := ⟨g * r.pc, r.fp⟩
  bc := ⟨r.pc, r.rbc, Opcode.mulNative.code, #v[r.oA, r.oB, r.oC, 0, 0, 0, 0]⟩
  mem := [⟨r.fp * r.oA, r.rA, r.vA⟩, ⟨r.fp * r.oB, r.rB, r.vB⟩,
    ⟨r.fp * r.oC, r.rC,
      #v[r.vA[0] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1],
         r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1] +
           r.vA[2] * r.vB[2],
         r.vA[0] * r.vB[2] + r.vA[1] * r.vB[1] + r.vA[2] * r.vB[0] + r.vA[2] * r.vB[2]]⟩]

/-- What a `SET_CONSTANT` row sends (specification §7.3): the fall-through step, the bytecode
tuple `(SET_CONSTANT, o, k₀, k₁, k₂, 0, 0, 0)`, and one memory read of `k` at `fp·o`. -/
def setSends (r : SetRow K) : OpcodeSends where
  pull := ⟨r.pc, r.fp⟩
  push := ⟨g * r.pc, r.fp⟩
  bc := ⟨r.pc, r.rbc, Opcode.setConstant.code, #v[r.o, r.k[0], r.k[1], r.k[2], 0, 0, 0]⟩
  mem := [⟨r.fp * r.o, r.r, r.k⟩]

/-- What a `DEREF` row sends (specification §7.4; `tables.rs:616-623`): the fall-through step,
the bytecode tuple `(DEREF, o₁, o₂, o₃, f_pc, f_fp, 0, 0)`, and three memory reads, the pointer,
the local word and the target, which carries the store coordinates of the flags. The reads are
in the specification's order; the Rust flushes the target before the local word, which balance,
a multiset equality, does not see. -/
def derefSends (r : DerefRow K) : OpcodeSends where
  pull := ⟨r.pc, r.fp⟩
  push := ⟨g * r.pc, r.fp⟩
  bc := ⟨r.pc, r.rbc, Opcode.deref.code, #v[r.o1, r.o2, r.o3, r.fpc, r.ffp, 0, 0]⟩
  mem := [⟨r.fp * r.o1, r.r1, #v[r.p, 0, 0]⟩, ⟨r.fp * r.o3, r.r3, r.v3⟩,
    ⟨r.p * r.o2, r.r2,
      #v[(1 + r.fpc + r.ffp) * r.v3[0] + r.fpc * (g ^ 2 * r.pc) + r.ffp * r.fp,
         (1 + r.fpc + r.ffp) * r.v3[1], (1 + r.fpc + r.ffp) * r.v3[2]]⟩]

/-- What a `JUMP` row with indicator `b` sends (specification §7.5; `tables.rs:724-760`): the
step to `(b·v_pc + b·g·pc + g·pc, b·v_fp + b·fp + fp)`, the bytecode tuple
`(JUMP, o_c, o_d, o_f, 0, 0, 0, 0)`, and three memory reads of `K` words. -/
def jumpSends (r : JumpRow K) (b : K) : OpcodeSends where
  pull := ⟨r.pc, r.fp⟩
  push := ⟨b * r.vpc + b * (g * r.pc) + g * r.pc, b * r.vfp + b * r.fp + r.fp⟩
  bc := ⟨r.pc, r.rbc, Opcode.jump.code, #v[r.oc, r.od, r.of, 0, 0, 0, 0]⟩
  mem := [⟨r.fp * r.oc, r.rc, #v[r.vcond, 0, 0]⟩, ⟨r.fp * r.od, r.rd, #v[r.vpc, 0, 0]⟩,
    ⟨r.fp * r.of, r.rf, #v[r.vfp, 0, 0]⟩]

/-- What a `BLAKE2S` row sends (specification §7.6; `tables.rs:833-900`): the fall-through step,
the bytecode tuple `(BLAKE2S, o_{m₀}, …, o_{m₃}, o_cv, o_out, o_md)`, and nine memory reads of
two-limb cells: the four message cells, the two chaining-value cells at `fp·o_cv` and
`fp·g·o_cv`, the two output cells likewise, and the metadata cell. -/
def blake2sSends (r : Blake2sRow K) : OpcodeSends where
  pull := ⟨r.pc, r.fp⟩
  push := ⟨g * r.pc, r.fp⟩
  bc := ⟨r.pc, r.rbc, Opcode.blake2s.code, #v[r.om0, r.om1, r.om2, r.om3, r.ocv, r.oout, r.omd]⟩
  mem := [⟨r.fp * r.om0, r.rm0, #v[r.m0[0], r.m0[1], 0]⟩,
    ⟨r.fp * r.om1, r.rm1, #v[r.m1[0], r.m1[1], 0]⟩,
    ⟨r.fp * r.om2, r.rm2, #v[r.m2[0], r.m2[1], 0]⟩,
    ⟨r.fp * r.om3, r.rm3, #v[r.m3[0], r.m3[1], 0]⟩,
    ⟨r.fp * r.ocv, r.rcv0, #v[r.cv0[0], r.cv0[1], 0]⟩,
    ⟨r.fp * (g * r.ocv), r.rcv1, #v[r.cv1[0], r.cv1[1], 0]⟩,
    ⟨r.fp * r.oout, r.rout0, #v[r.out0[0], r.out0[1], 0]⟩,
    ⟨r.fp * (g * r.oout), r.rout1, #v[r.out1[0], r.out1[1], 0]⟩,
    ⟨r.fp * r.omd, r.rmd, #v[r.md[0], r.md[1], 0]⟩]

/-- The messages the verifier sends on the channel `c` in the direction `d`: Clean's
`activeMessages` of its interactions on the channel of that name. -/
def verifierMessagesOn {prog : Program} {κ : ℕ} (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (c : RawChannel K) (d : BusDir) : List (Array K) :=
  activeMessages (((leanIsaEnsemble prog κ).verifierOperations.interactionValues
    (.fromInput w.publicInput w.data)).filter (·.channel.name = c.name)) d

/-! ## Proof helpers -/

/-- The sends of an opcode row, in the order the tables emit them: the state pull and push, the
bytecode read, then each memory read. -/
private def OpcodeSends.sends (s : OpcodeSends) : List (String × BusDir × Array K) :=
  [(StateChannel.name, .pull, #[s.pull.pc, s.pull.fp]),
    (StateChannel.name, .push, #[s.push.pc, s.push.fp]),
    (BytecodeChannel.name, .pull, (toElements s.bc).toArray),
    (BytecodeChannel.name, .push, (toElements s.bc.bump).toArray)] ++
  s.mem.flatMap fun m ↦ [(MemChannel.name, .pull, (toElements m).toArray),
    (MemChannel.name, .push, (toElements m.bump).toArray)]

/-- An opcode row whose circuit, every interaction of multiplicity `1`, sends the sends of `s`
sends `s`. -/
private theorem sendsOpcode_of_sends {t : Air.Flat.Table K}
    (hm : ∀ i ∈ t.component.rowOperations.interactions, i.mult = 1) (row : Array K)
    {s : OpcodeSends} (h : rowSends t.component (t.environment row) = s.sends) :
    SendsOpcode t row s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [rowMessagesOn_eq_rowSends t row _ _ hm, h]
    simp [chanOf, OpcodeSends.sends, Channel.toRaw_name, StateChannel, MemChannel,
      BytecodeChannel, List.filter_flatMap, List.map_flatMap, ← List.map_eq_flatMap]

/-- Evaluates the closed form of an opcode row's sends against the sends `s`. -/
local macro "eval_sends" s:ident : tactic => `(tactic|
  simp [OpcodeSends.sends, $s:ident, memMsg_toArray, bytecodeMsg_toArray, MemMsg.bump,
    BytecodeMsg.bump])

/-! ## The six opcode tables -/

-- Each `*_rowSends` evaluates the closed form at a row variable that evaluates to a free row
-- `r`, the typed row substituted afterwards: at the typed row itself the kernel unfolds it while
-- it checks the rewrites.

/-- The sends of an `XOR` row circuit, at a row variable that evaluates to `r`. -/
private theorem xor_rowSends (env : Environment K) (r : XorRow K)
    (hr : eval env (varFromOffset XorRow 0 : Var XorRow K) = r) :
    rowSends xorComponent env = (xorSends r).sends := by
  rw [show rowSends xorComponent _ = _ from xor_sends_gen _ _ _ _ hr]
  eval_sends xorSends

/-- Every row of an `XOR` table sends `xorSends` of its typed row. -/
theorem xor_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = xorComponent)
    (row : Array K) :
    SendsOpcode t row (xorSends (valueFromOffset XorRow 0 (t.environment row))) :=
  sendsOpcode_of_sends (ht ▸ xor_mults_gen _ _) row (by
    rw [ht]
    exact xor_rowSends _ _ (eval_varFromOffset_valueFromOffset XorRow 0 _))

/-- The sends of a `MUL_NATIVE` row circuit, at a row variable that evaluates to `r`. -/
private theorem mul_rowSends (env : Environment K) (r : MulRow K)
    (hr : eval env (varFromOffset MulRow 0 : Var MulRow K) = r) :
    rowSends mulComponent env = (mulSends r).sends := by
  rw [show rowSends mulComponent _ = _ from mul_sends_gen _ _ _ _ hr]
  eval_sends mulSends

/-- Every row of a `MUL_NATIVE` table sends `mulSends` of its typed row. -/
theorem mul_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = mulComponent)
    (row : Array K) :
    SendsOpcode t row (mulSends (valueFromOffset MulRow 0 (t.environment row))) :=
  sendsOpcode_of_sends (ht ▸ mul_mults_gen _ _) row (by
    rw [ht]
    exact mul_rowSends _ _ (eval_varFromOffset_valueFromOffset MulRow 0 _))

/-- The sends of a `SET_CONSTANT` row circuit, at a row variable that evaluates to `r`. -/
private theorem set_rowSends (env : Environment K) (r : SetRow K)
    (hr : eval env (varFromOffset SetRow 0 : Var SetRow K) = r) :
    rowSends setComponent env = (setSends r).sends := by
  rw [show rowSends setComponent _ = _ from set_sends_gen _ _ _ _ hr]
  eval_sends setSends

/-- Every row of a `SET_CONSTANT` table sends `setSends` of its typed row. -/
theorem set_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = setComponent)
    (row : Array K) :
    SendsOpcode t row (setSends (valueFromOffset SetRow 0 (t.environment row))) :=
  sendsOpcode_of_sends (ht ▸ set_mults_gen _ _) row (by
    rw [ht]
    exact set_rowSends _ _ (eval_varFromOffset_valueFromOffset SetRow 0 _))

/-- The sends of a `DEREF` row circuit, at a row variable that evaluates to `r`. -/
private theorem deref_rowSends (env : Environment K) (r : DerefRow K)
    (hr : eval env (varFromOffset DerefRow 0 : Var DerefRow K) = r) :
    rowSends derefComponent env = (derefSends r).sends := by
  rw [show rowSends derefComponent _ = _ from deref_sends_gen _ _ _ _ hr]
  eval_sends derefSends

/-- Every row of a `DEREF` table sends `derefSends` of its typed row. -/
theorem deref_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = derefComponent)
    (row : Array K) :
    SendsOpcode t row (derefSends (valueFromOffset DerefRow 0 (t.environment row))) :=
  sendsOpcode_of_sends (ht ▸ deref_mults_gen _ _) row (by
    rw [ht]
    exact deref_rowSends _ _ (eval_varFromOffset_valueFromOffset DerefRow 0 _))

/-- The sends of a `JUMP` row circuit, at a row variable that evaluates to `r` and with the
indicator `b` at the second local witness slot. -/
private theorem jump_rowSends (env : Environment K) (r : JumpRow K)
    (hr : eval env (varFromOffset JumpRow 0 : Var JumpRow K) = r) (b : K)
    (hb : env.get (size JumpRow + 1) = b) : rowSends jumpComponent env = (jumpSends r b).sends := by
  rw [show rowSends jumpComponent _ = _ from jump_sends_gen _ _ _ _ hr b hb]
  eval_sends jumpSends

/-- Every row of a `JUMP` table sends `jumpSends` of its typed row and its indicator, the raw
cell after its columns and its inverse witness. -/
theorem jump_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = jumpComponent)
    (row : Array K) :
    SendsOpcode t row (jumpSends (valueFromOffset JumpRow 0 (t.environment row))
      (row[size JumpRow + 1]?.getD 0)) :=
  sendsOpcode_of_sends (ht ▸ jump_mults_gen _ _) row (by
    rw [ht]
    exact jump_rowSends _ _ (eval_varFromOffset_valueFromOffset JumpRow 0 _) _ rfl)

/-- The sends of a `BLAKE2S` row circuit, at a row variable that evaluates to `r`. -/
private theorem blake2s_rowSends (env : Environment K) (r : Blake2sRow K)
    (hr : eval env (varFromOffset Blake2sRow 0 : Var Blake2sRow K) = r) :
    rowSends blake2sComponent env = (blake2sSends r).sends := by
  rw [show rowSends blake2sComponent _ = _ from blake2s_sends_gen _ _ _ _ hr]
  eval_sends blake2sSends

/-- Every row of a `BLAKE2S` table sends `blake2sSends` of its typed row. -/
theorem blake2s_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = blake2sComponent)
    (row : Array K) :
    SendsOpcode t row (blake2sSends (valueFromOffset Blake2sRow 0 (t.environment row))) :=
  sendsOpcode_of_sends (ht ▸ blake2s_mults_gen _ _) row (by
    rw [ht]
    exact blake2s_rowSends _ _ (eval_varFromOffset_valueFromOffset Blake2sRow 0 _))

/-! ## The blocks and the verifier -/

/-- A push and a pull on one channel, read on a channel name and a direction. -/
private theorem chanOf_two (a : String) (u v : Array K) (c : String) (d : BusDir) :
    chanOf c d [(a, .push, u), (a, .pull, v)] =
      if c = a then if d = .push then [u] else [v] else [] := by
  by_cases h : c = a
  · subst h
    cases d <;> simp [chanOf]
  · simp [chanOf, Ne.symm h, h]

/-- A row of the memory block pushes its seed `(idx, 1, m)` and pulls its finalize
`(idx, cntFin, m)` on the memory channel, and sends nothing on any other channel (specification
§6.2 "Seed" and "Finalize"; `layout.rs:359-382`). -/
theorem memBlock_rowMessagesOn {κ : ℕ} {t : Air.Flat.Table K} (ht : t.component = memComponent κ)
    (row : Array K) {r : MemRow K} (hr : valueFromOffset MemRow 0 (t.environment row) = r)
    (c : RawChannel K) (d : BusDir) :
    rowMessagesOn t row c d =
      if c.name = MemChannel.name then
        if d = .push then [(toElements (⟨r.idx, 1, r.m⟩ : MemMsg K)).toArray]
        else [(toElements (⟨r.idx, r.cntFin, r.m⟩ : MemMsg K)).toArray]
      else [] := by
  rw [rowMessagesOn_eq_rowSends t row c d (ht ▸ mem_mults κ), ht,
    show rowSends (memComponent κ) _ = _ from mem_sends_gen _ _ _ _
      ((eval_varFromOffset_valueFromOffset MemRow 0 _).trans hr),
    chanOf_two, memMsg_toArray, memMsg_toArray]

/-- A row of the bytecode block pushes its seed `(idx, 1, opcode, op)` and pulls its finalize
`(idx, cntFin, opcode, op)` on the bytecode channel, and sends nothing on any other channel
(specification §6.2, §6.4; `layout.rs:383-395`). -/
theorem bytecodeBlock_rowMessagesOn {prog : Program} {t : Air.Flat.Table K}
    (ht : t.component = bytecodeComponent prog) (row : Array K) {r : BytecodeRow K}
    (hr : valueFromOffset BytecodeRow 0 (t.environment row) = r) (c : RawChannel K)
    (d : BusDir) :
    rowMessagesOn t row c d =
      if c.name = BytecodeChannel.name then
        if d = .push then [(toElements (⟨r.idx, 1, r.opcode, r.op⟩ : BytecodeMsg K)).toArray]
        else [(toElements (⟨r.idx, r.cntFin, r.opcode, r.op⟩ : BytecodeMsg K)).toArray]
      else [] := by
  rw [rowMessagesOn_eq_rowSends t row c d (ht ▸ bytecode_mults prog), ht,
    show rowSends (bytecodeComponent prog) _ = _ from bytecode_sends_gen _ _ _ _
      ((eval_varFromOffset_valueFromOffset BytecodeRow 0 _).trans hr),
    chanOf_two, bytecodeMsg_toArray, bytecodeMsg_toArray]

/-- The verifier pushes `(1, 1)` and pulls `(g^(N_prog - 1), 1)` on the state channel, and
sends nothing on any other channel (specification §6.1; `layout.rs:352-358`). -/
theorem verifier_messagesOn {prog : Program} {κ : ℕ}
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) (c : RawChannel K) (d : BusDir) :
    verifierMessagesOn w c d =
      if c.name = StateChannel.name then
        if d = .push then [#[1, 1]] else [#[prog.finalPc, 1]]
      else [] := by
  rw [verifierMessagesOn, activeMessages_filter_name _
    (fun i hi ↦ by rw [verifier_mults prog κ _ i hi]; exact one_ne_zero), verifier_sends,
    chanOf_two]

/-! ## The witness -/

variable {prog : Program} {κ : ℕ}

/-- The messages a witness sends on a channel in a direction are the verifier's, then its rows',
table by table and row by row. -/
theorem messagesOn_eq_flatMap (w : EnsembleWitness (leanIsaEnsemble prog κ)) (c : RawChannel K)
    (d : BusDir) :
    messagesOn w c d = verifierMessagesOn w c d ++
      w.tables.flatMap fun t ↦ t.table.flatMap fun row ↦ rowMessagesOn t row c d := by
  simp only [messagesOn, verifierMessagesOn, rowMessagesOn, activeMessages,
    EnsembleWitness.interactions, Air.Flat.Table.interactions, List.filter_append,
    List.filter_flatMap, List.map_append, List.map_flatMap]

/-- Every interaction of a witness has multiplicity `1`: every component and the verifier
interact through Clean's `pull` and `push` only. -/
theorem interactions_mult_eq_one (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    ∀ i ∈ w.interactions, i.mult = 1 := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact verifier_mults prog κ _ i hi
  obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp hi
  rw [table_interactions_eq] at hi
  obtain ⟨row, -, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  refine eval_mult_eq_one ?_ _
  have hc := EnsembleWitness.component_mem_tables_of_mem ht
  simp only [leanIsaEnsemble, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h | h | h | h | h <;> rw [h] at hj
  exacts [xor_mults_gen _ _ j hj, mul_mults_gen _ _ j hj, set_mults_gen _ _ j hj,
    deref_mults_gen _ _ j hj, jump_mults_gen _ _ j hj, blake2s_mults_gen _ _ j hj,
    mem_mults κ j hj, bytecode_mults prog j hj]

/-- Every row of the six opcode tables of a witness sends an `OpcodeSends`, with at most nine
memory reads (`BLAKE2S`'s nine). -/
theorem exists_sendsOpcode (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    ∀ t ∈ w.tables.take 6, ∀ row, ∃ s, SendsOpcode t row s ∧ s.mem.length ≤ 9 := by
  intro t ht row
  rw [List.mem_iff_getElem] at ht
  obtain ⟨i, hi, rfl⟩ := ht
  have hi6 : i < 6 := lt_of_lt_of_le hi (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have h8 : i < 8 := by omega
  rw [List.getElem_take]
  have hc : (w.tables[i]'(by rw [← w.same_length]; exact h8)).component =
      (leanIsaEnsemble prog κ).tables[i]'h8 := (w.same_circuits i h8).symm
  interval_cases i
  · exact ⟨_, xor_sendsOpcode hc row, by simp [xorSends]⟩
  · exact ⟨_, mul_sendsOpcode hc row, by simp [mulSends]⟩
  · exact ⟨_, set_sendsOpcode hc row, by simp [setSends]⟩
  · exact ⟨_, deref_sendsOpcode hc row, by simp [derefSends]⟩
  · exact ⟨_, jump_sendsOpcode hc row, by simp [jumpSends]⟩
  · exact ⟨_, blake2s_sendsOpcode hc row, by simp [blake2sSends]⟩

/-- A message a row sends is the message of one of its table's interactions on a channel of that
name and in that direction. -/
theorem exists_interaction_of_mem_rowMessagesOn {t : Air.Flat.Table K} {row : Array K}
    (hrow : row ∈ t.table) {c : RawChannel K} {d : BusDir} {a : Array K}
    (ha : a ∈ rowMessagesOn t row c d) :
    ∃ i ∈ t.interactions, i.channel.name = c.name ∧ i.direction = d ∧ i.msg = a := by
  rw [rowMessagesOn, activeMessages, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  simp only [List.mem_filter, decide_eq_true_eq] at hi
  exact ⟨i, List.mem_flatMap.mpr ⟨row, hrow, hi.1.1⟩, hi.1.2, hi.2.1, rfl⟩

/-- A message a row of a witness's table sends is a message of the witness on that channel and
in that direction. -/
theorem mem_messagesOn_of_mem_rowMessagesOn {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    {t : Air.Flat.Table K} (ht : t ∈ w.tables) {row : Array K} (hrow : row ∈ t.table)
    {c : RawChannel K} {d : BusDir} {a : Array K} (ha : a ∈ rowMessagesOn t row c d) :
    a ∈ messagesOn w c d := by
  rw [messagesOn_eq_flatMap, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨t, ht, List.mem_flatMap.mpr ⟨row, hrow, ha⟩⟩

/-- A message of a witness on a channel in a direction is the message of one of its interactions
on a channel of that name and in that direction. -/
theorem exists_interaction_of_mem_messagesOn {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    {c : RawChannel K} {d : BusDir} {a : Array K} (ha : a ∈ messagesOn w c d) :
    ∃ i ∈ w.interactions, i.channel.name = c.name ∧ i.direction = d ∧ i.msg = a := by
  rw [messagesOn, activeMessages, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  simp only [List.mem_filter, decide_eq_true_eq] at hi
  exact ⟨i, hi.1.1, hi.1.2, hi.2.1, rfl⟩

/-- The message of an interaction of a witness is a message of the witness on its channel and in
its direction: no interaction is inactive (`interactions_mult_eq_one`). -/
theorem mem_messagesOn_of_mem_interactions {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    {i : Interaction K} (hi : i ∈ w.interactions) {c : RawChannel K}
    (hname : i.channel.name = c.name) : i.msg ∈ messagesOn w c i.direction := by
  have h1 := interactions_mult_eq_one w i hi
  refine List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hi, ?_⟩, ?_⟩) <;>
    simp only [decide_eq_true_eq, true_and]
  · exact hname
  · rw [h1]
    exact one_ne_zero

end LeanerVM.Arithmetization
