/-
  LeanerVM.Arithmetization.Rows

  What one row of each component of the leanISA ensemble sends on the bus, in closed form on
  arbitrary raw rows: the six opcode tables, the memory and bytecode blocks, and the verifier.
-/

module

public import LeanerVM.Arithmetization.Statement

@[expose] public section

/-!
# What a row sends

The messages one row of a component sends on each of the six channels, as functions of the
row's typed input `valueFromOffset Row 0 (t.environment row)`, Clean's `Component.rowInput`:
the first `size Row` cells of the raw row read as the typed row, a missing cell `0`. The rows
are arbitrary, honest or not, and nothing about the constraints is assumed. Category A: facts
about this repository's circuits, which transcribe leanVM at pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` (specification §5.1 "The bus", §6, §7;
`crates/lean_vm/src/tables.rs`, `cpu/layout.rs:352-395`).

**Opcode rows.** A row of each of the six opcode tables sends an `OpcodeSends`: it pulls its
state `pull`, pushes `push`, reads its bytecode tuple `bc`, and reads the memory tuples `mem`.
A read pulls its tuple and pushes it with the count multiplied by `g` (§6.2 "Flush rules"), so
the pushes on the two lookup channels are the pulls, `bump`ed. `SendsOpcode t row s` states
the messages of `s` on each of the six channels; `xorSends`, `mulSends`, `setSends`,
`derefSends`, `jumpSends` and `blake2sSends` are the tables' sends, and `xor_sendsOpcode` and
its five siblings say that every row of a table sends them. Per row: one state pull and push,
one bytecode read, and three memory reads (`XOR`, `MUL_NATIVE`, `DEREF`, `JUMP`), one
(`SET_CONSTANT`) or nine (`BLAKE2S`).

**Blocks and verifier.** A memory block row pushes its seed `(idx, 1, m)` and pulls its
finalize `(idx, cntFin, m)`, a bytecode block row likewise (§6.2 "Seed" and "Finalize"), and
the verifier pushes `(1, 1)` and pulls `(g^(N_prog - 1), 1)` (§6.1). Every other channel
carries nothing from them.

**The witness.** `messagesOn_eq_flatMap` reads the messages a witness sends on a channel as
its rows' messages, table by table, and `exists_sendsOpcode` says every row of the six opcode
tables sends some `OpcodeSends` with at most nine memory reads.

The proofs evaluate each row circuit once over a row variable `x` with `eval env x = r` and
specialize it at Clean's `varFromOffset` (`eval_varFromOffset_valueFromOffset`), the technique
of `Completeness/Messages.lean` in leanerVM pull request #83.

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
  state_pull : rowMessagesOn t row StatePull.toRaw = [#[s.pull.pc, s.pull.fp]]
  /-- The state pushed. -/
  state_push : rowMessagesOn t row StatePush.toRaw = [#[s.push.pc, s.push.fp]]
  /-- The bytecode read's pull. -/
  bytecode_pull : rowMessagesOn t row BytecodePull.toRaw = [(toElements s.bc).toArray]
  /-- The bytecode read's push. -/
  bytecode_push : rowMessagesOn t row BytecodePush.toRaw = [(toElements s.bc.bump).toArray]
  /-- The memory reads' pulls. -/
  mem_pull : rowMessagesOn t row MemPull.toRaw = s.mem.map fun m ↦ (toElements m).toArray
  /-- The memory reads' pushes. -/
  mem_push : rowMessagesOn t row MemPush.toRaw = s.mem.map fun m ↦ (toElements m.bump).toArray

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
the local word and the target, which carries the store coordinates of the flags. -/
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

/-! ## Proof helpers -/

/-- The `(channel name, message)` pairs of an opcode row's sends, in the order the tables emit
them: the state pull and push, the bytecode read, then each memory read. -/
private def OpcodeSends.pairs (s : OpcodeSends) : List (String × Array K) :=
  [(StatePull.name, (toElements s.pull).toArray), (StatePush.name, (toElements s.push).toArray),
    (BytecodePull.name, (toElements s.bc).toArray),
    (BytecodePush.name, (toElements s.bc.bump).toArray)] ++
  s.mem.flatMap fun m ↦ [(MemPull.name, (toElements m).toArray),
    (MemPush.name, (toElements m.bump).toArray)]

/-- Evaluating a typed message's elements is evaluating the message. -/
private theorem map_eval_toElements {M : TypeMap} [ProvableType M] (env : Environment K)
    (x : M (Expression K)) :
    (toElements x).map (Expression.eval env) = toElements (eval env x) :=
  (ProvableType.toElements_eval env x).symm

/-- A state message is the array `[pc, fp]`. -/
private theorem regs_toArray (s : Regs K) : (toElements s).toArray = #[s.pc, s.fp] := by
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray, regs_toElements]

-- Each `*_pairs` proof below writes the vector fields of both rows as literals and substitutes
-- the typed row's fields by their evaluations before it evaluates the circuit: a projection of
-- an evaluated vector left under a product makes the kernel unfold multiplication in `K`, and
-- in a module the check does not return.

/-- A vector of three is a literal. -/
private theorem exists_vector_three {α : Type} (v : Vector α 3) : ∃ a b c, v = #v[a, b, c] :=
  ⟨v[0], v[1], v[2], by ext i hi; interval_cases i <;> rfl⟩

/-- A vector of two is a literal. -/
private theorem exists_vector_two {α : Type} (v : Vector α 2) : ∃ a b, v = #v[a, b] :=
  ⟨v[0], v[1], by ext i hi; interval_cases i <;> rfl⟩

/-- A row's messages on a channel, read off the `(channel name, message)` pairs its row circuit
sends at the row variable. -/
private theorem rowMessagesOn_eq_pairs {Input Output : TypeMap} [ProvableType Input]
    [ProvableType Output] {circuit : GeneralFormalCircuit K Input Output} {t : Air.Flat.Table K}
    (ht : t.component = ⟨circuit⟩) (row : Array K) (c : RawChannel K) :
    rowMessagesOn t row c =
      (((((circuit.main (varFromOffset Input 0)).operations (size Input)).interactionValues
        (t.environment row)).map fun i : Interaction K ↦ (i.channel.name, i.msg)).filter
          fun p : String × Array K ↦ p.1 = c.name).map (·.2) := by
  rw [rowMessagesOn, ht, Component.interactionsValues_eq, Component.rowOperations_mk,
    List.filter_map, List.map_map]
  rfl

/-- An opcode row whose circuit sends the pairs of `s` sends `s`. -/
private theorem sendsOpcode_of_pairs {Input Output : TypeMap} [ProvableType Input]
    [ProvableType Output] {circuit : GeneralFormalCircuit K Input Output} {t : Air.Flat.Table K}
    (ht : t.component = ⟨circuit⟩) (row : Array K) {s : OpcodeSends}
    (h : (((circuit.main (varFromOffset Input 0)).operations (size Input)).interactionValues
      (t.environment row)).map (fun i ↦ (i.channel.name, i.msg)) = s.pairs) :
    SendsOpcode t row s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [rowMessagesOn_eq_pairs ht, h, OpcodeSends.pairs]
    simp only [List.cons_append, List.nil_append, List.filter_cons, List.filter_flatMap,
      Channel.toRaw_name, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      String.reduceEq, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false,
      List.filter_nil, List.map_cons, regs_toArray]
    simp [List.map_flatMap, ← List.map_eq_flatMap]

/-! ## The six opcode tables -/

/-- The pairs an `XOR` row circuit sends, at a row variable that evaluates to `r`. -/
private theorem xor_pairs (x : Var XorRow K) (env : Environment K) (n : ℕ) (r : XorRow K)
    (hx : eval env x = r) :
    (((xorTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) = (xorSends r).pairs := by
  obtain ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ := x
  obtain ⟨a0, a1, a2, rfl⟩ := exists_vector_three vA
  obtain ⟨b0, b1, b2, rfl⟩ := exists_vector_three vB
  obtain ⟨pc', fp', oA', oB', oC', vA', vB', rA', rB', rC', rbc'⟩ := r
  obtain ⟨a0', a1', a2', rfl⟩ := exists_vector_three vA'
  obtain ⟨b0', b1', b2', rfl⟩ := exists_vector_three vB'
  simp only [circuit_norm, Vector.map_mk, List.map_toArray, List.map_cons,
    List.map_nil, Vector.mk.injEq, XorRow.mk.injEq] at hx
  obtain ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := hx
  simp only [Operations.interactionValues, circuit_norm, xorTable, instructionStep, memRead,
    bytecodeRead, AbstractInteraction.eval, map_eval_toElements, xorSends, OpcodeSends.pairs,
    MemMsg.bump, BytecodeMsg.bump, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, -BitVec.reduceNeg]

/-- Every row of an `XOR` table sends `xorSends` of its typed row. -/
theorem xor_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = ⟨xorTable⟩) (row : Array K) :
    SendsOpcode t row (xorSends (valueFromOffset XorRow 0 (t.environment row))) :=
  sendsOpcode_of_pairs ht row
    (xor_pairs _ _ _ _ (eval_varFromOffset_valueFromOffset XorRow 0 (t.environment row)))

/-- The pairs a `MUL_NATIVE` row circuit sends, at a row variable that evaluates to `r`. -/
private theorem mul_pairs (x : Var MulRow K) (env : Environment K) (n : ℕ) (r : MulRow K)
    (hx : eval env x = r) :
    (((mulTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) = (mulSends r).pairs := by
  obtain ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ := x
  obtain ⟨a0, a1, a2, rfl⟩ := exists_vector_three vA
  obtain ⟨b0, b1, b2, rfl⟩ := exists_vector_three vB
  obtain ⟨pc', fp', oA', oB', oC', vA', vB', rA', rB', rC', rbc'⟩ := r
  obtain ⟨a0', a1', a2', rfl⟩ := exists_vector_three vA'
  obtain ⟨b0', b1', b2', rfl⟩ := exists_vector_three vB'
  simp only [circuit_norm, Vector.map_mk, List.map_toArray, List.map_cons,
    List.map_nil, Vector.mk.injEq, XorRow.mk.injEq] at hx
  obtain ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := hx
  simp only [Operations.interactionValues, circuit_norm, mulTable, instructionStep, memRead,
    bytecodeRead, AbstractInteraction.eval, map_eval_toElements, mulSends, OpcodeSends.pairs,
    MemMsg.bump, BytecodeMsg.bump, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, -BitVec.reduceNeg]

/-- Every row of a `MUL_NATIVE` table sends `mulSends` of its typed row. -/
theorem mul_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = ⟨mulTable⟩) (row : Array K) :
    SendsOpcode t row (mulSends (valueFromOffset MulRow 0 (t.environment row))) :=
  sendsOpcode_of_pairs ht row
    (mul_pairs _ _ _ _ (eval_varFromOffset_valueFromOffset MulRow 0 (t.environment row)))

/-- The pairs a `SET_CONSTANT` row circuit sends, at a row variable that evaluates to `r`. -/
private theorem set_pairs (x : Var SetRow K) (env : Environment K) (n : ℕ) (r : SetRow K)
    (hx : eval env x = r) :
    (((setTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) = (setSends r).pairs := by
  obtain ⟨pc, fp, o, k, rc, rbc⟩ := x
  obtain ⟨k0, k1, k2, rfl⟩ := exists_vector_three k
  obtain ⟨pc', fp', o', k', rc', rbc'⟩ := r
  obtain ⟨k0', k1', k2', rfl⟩ := exists_vector_three k'
  simp only [circuit_norm, Vector.map_mk, List.map_toArray, List.map_cons,
    List.map_nil, Vector.mk.injEq, SetRow.mk.injEq] at hx
  obtain ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := hx
  simp only [Operations.interactionValues, circuit_norm, setTable, instructionStep, memRead,
    bytecodeRead, AbstractInteraction.eval, map_eval_toElements, setSends, OpcodeSends.pairs,
    MemMsg.bump, BytecodeMsg.bump, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, -BitVec.reduceNeg]

/-- Every row of a `SET_CONSTANT` table sends `setSends` of its typed row. -/
theorem set_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = ⟨setTable⟩) (row : Array K) :
    SendsOpcode t row (setSends (valueFromOffset SetRow 0 (t.environment row))) :=
  sendsOpcode_of_pairs ht row
    (set_pairs _ _ _ _ (eval_varFromOffset_valueFromOffset SetRow 0 (t.environment row)))

/-- The pairs a `DEREF` row circuit sends, at a row variable that evaluates to `r`. -/
private theorem deref_pairs (x : Var DerefRow K) (env : Environment K) (n : ℕ) (r : DerefRow K)
    (hx : eval env x = r) :
    (((derefTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) = (derefSends r).pairs := by
  obtain ⟨pc, fp, o1, o2, o3, fpc, ffp, p, v3, r1, r2, r3, rbc⟩ := x
  obtain ⟨a0, a1, a2, rfl⟩ := exists_vector_three v3
  obtain ⟨pc', fp', o1', o2', o3', fpc', ffp', p', v3', r1', r2', r3', rbc'⟩ := r
  obtain ⟨a0', a1', a2', rfl⟩ := exists_vector_three v3'
  simp only [circuit_norm, Vector.map_mk, List.map_toArray, List.map_cons,
    List.map_nil, Vector.mk.injEq, DerefRow.mk.injEq] at hx
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := hx
  simp only [Operations.interactionValues, circuit_norm, derefTable, instructionStep, memRead,
    bytecodeRead, AbstractInteraction.eval, map_eval_toElements, derefSends, OpcodeSends.pairs,
    MemMsg.bump, BytecodeMsg.bump, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, -BitVec.reduceNeg]

/-- Every row of a `DEREF` table sends `derefSends` of its typed row. -/
theorem deref_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = ⟨derefTable⟩)
    (row : Array K) :
    SendsOpcode t row (derefSends (valueFromOffset DerefRow 0 (t.environment row))) :=
  sendsOpcode_of_pairs ht row
    (deref_pairs _ _ _ _ (eval_varFromOffset_valueFromOffset DerefRow 0 (t.environment row)))

/-- The pairs a `JUMP` row circuit sends, at a row variable that evaluates to `r` and with the
indicator `b` at the second local witness slot. -/
private theorem jump_pairs (x : Var JumpRow K) (env : Environment K) (n : ℕ) (r : JumpRow K)
    (hx : eval env x = r) :
    (((jumpTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) = (jumpSends r (env.get (n + 1))).pairs := by
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := x
  obtain ⟨pc', fp', oc', od', of', vcond', vpc', vfp', rc', rd', rf', rbc'⟩ := r
  simp only [circuit_norm, JumpRow.mk.injEq] at hx
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hx
  dsimp only [jumpTable]
  simp only [Operations.interactionValues, circuit_norm, instructionStep, memRead,
    bytecodeRead, AbstractInteraction.eval, map_eval_toElements, jumpSends, OpcodeSends.pairs,
    MemMsg.bump, BytecodeMsg.bump, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, -BitVec.reduceNeg]

/-- Every row of a `JUMP` table sends `jumpSends` of its typed row and its indicator, the raw
cell after its columns and its inverse witness. -/
theorem jump_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = ⟨jumpTable⟩)
    (row : Array K) :
    SendsOpcode t row (jumpSends (valueFromOffset JumpRow 0 (t.environment row))
      (row[size JumpRow + 1]?.getD 0)) :=
  sendsOpcode_of_pairs ht row
    (jump_pairs _ _ _ _ (eval_varFromOffset_valueFromOffset JumpRow 0 (t.environment row)))

/-- The pairs a `BLAKE2S` row circuit sends, at a row variable that evaluates to `r`. -/
private theorem blake2s_pairs (x : Var Blake2sRow K) (env : Environment K) (n : ℕ)
    (r : Blake2sRow K) (hx : eval env x = r) :
    (((blake2sTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) = (blake2sSends r).pairs := by
  obtain ⟨pc, fp, om0, om1, om2, om3, ocv, oout, omd, m0, m1, m2, m3, out0, out1, cv0, cv1, md,
    rm0, rm1, rm2, rm3, rcv0, rcv1, rout0, rout1, rmd, rbc⟩ := x
  obtain ⟨m0a, m0b, rfl⟩ := exists_vector_two m0
  obtain ⟨m1a, m1b, rfl⟩ := exists_vector_two m1
  obtain ⟨m2a, m2b, rfl⟩ := exists_vector_two m2
  obtain ⟨m3a, m3b, rfl⟩ := exists_vector_two m3
  obtain ⟨out0a, out0b, rfl⟩ := exists_vector_two out0
  obtain ⟨out1a, out1b, rfl⟩ := exists_vector_two out1
  obtain ⟨cv0a, cv0b, rfl⟩ := exists_vector_two cv0
  obtain ⟨cv1a, cv1b, rfl⟩ := exists_vector_two cv1
  obtain ⟨mda, mdb, rfl⟩ := exists_vector_two md
  obtain ⟨pc', fp', om0', om1', om2', om3', ocv', oout', omd', m0', m1', m2', m3', out0', out1',
    cv0', cv1', md', rm0', rm1', rm2', rm3', rcv0', rcv1', rout0', rout1', rmd', rbc'⟩ := r
  obtain ⟨m0a', m0b', rfl⟩ := exists_vector_two m0'
  obtain ⟨m1a', m1b', rfl⟩ := exists_vector_two m1'
  obtain ⟨m2a', m2b', rfl⟩ := exists_vector_two m2'
  obtain ⟨m3a', m3b', rfl⟩ := exists_vector_two m3'
  obtain ⟨out0a', out0b', rfl⟩ := exists_vector_two out0'
  obtain ⟨out1a', out1b', rfl⟩ := exists_vector_two out1'
  obtain ⟨cv0a', cv0b', rfl⟩ := exists_vector_two cv0'
  obtain ⟨cv1a', cv1b', rfl⟩ := exists_vector_two cv1'
  obtain ⟨mda', mdb', rfl⟩ := exists_vector_two md'
  simp only [circuit_norm, Vector.map_mk, List.map_toArray, List.map_cons,
    List.map_nil, Vector.mk.injEq, Blake2sRow.mk.injEq] at hx
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩ := hx
  simp only [Operations.interactionValues, circuit_norm, blake2sTable, instructionStep, memRead,
    bytecodeRead, AbstractInteraction.eval, map_eval_toElements, blake2sSends, OpcodeSends.pairs,
    MemMsg.bump, BytecodeMsg.bump, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, -BitVec.reduceNeg]

/-- Every row of a `BLAKE2S` table sends `blake2sSends` of its typed row. -/
theorem blake2s_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = ⟨blake2sTable⟩)
    (row : Array K) :
    SendsOpcode t row (blake2sSends (valueFromOffset Blake2sRow 0 (t.environment row))) :=
  sendsOpcode_of_pairs ht row
    (blake2s_pairs _ _ _ _ (eval_varFromOffset_valueFromOffset Blake2sRow 0 (t.environment row)))

/-! ## The blocks and the verifier -/

/-- The pairs a memory block row circuit sends, at a row variable that evaluates to `r`. -/
private theorem mem_pairs (x : Var MemRow K) (env : Environment K) (n : ℕ) (r : MemRow K)
    (hx : eval env x = r) :
    (((memTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(MemPush.name, (toElements (⟨r.idx, 1, r.m⟩ : MemMsg K)).toArray),
        (MemPull.name, (toElements (⟨r.idx, r.cntFin, r.m⟩ : MemMsg K)).toArray)] := by
  subst hx
  obtain ⟨idx, cntFin, m⟩ := x
  simp only [Operations.interactionValues, circuit_norm, memTable, AbstractInteraction.eval,
    map_eval_toElements, -BitVec.reduceNeg]

/-- The pairs a bytecode block row circuit sends, at a row variable that evaluates to `r`. -/
private theorem bytecode_pairs (x : Var BytecodeRow K) (env : Environment K) (n : ℕ)
    (r : BytecodeRow K) (hx : eval env x = r) :
    (((bytecodeTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(BytecodePush.name, (toElements (⟨r.idx, 1, r.opcode, r.op⟩ : BytecodeMsg K)).toArray),
        (BytecodePull.name,
          (toElements (⟨r.idx, r.cntFin, r.opcode, r.op⟩ : BytecodeMsg K)).toArray)] := by
  subst hx
  obtain ⟨idx, cntFin, opcode, op⟩ := x
  simp only [Operations.interactionValues, circuit_norm, bytecodeTable, AbstractInteraction.eval,
    map_eval_toElements, -BitVec.reduceNeg]

/-- The pairs the verifier's circuit sends, whatever its input. -/
private theorem verifier_pairs (prog : Program) (x : Var PublicIO K) (env : Environment K)
    (n : ℕ) :
    ((((leanIsaVerifier prog).main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] := by
  simp only [Operations.interactionValues, circuit_norm, leanIsaVerifier, AbstractInteraction.eval,
    map_eval_toElements, regs_toArray, -BitVec.reduceNeg]

/-- Filtering two pairs with distinct names by a name. -/
private theorem filter_two {a b : String} (hab : a ≠ b) (u v : Array K) (c : String) :
    ((([(a, u), (b, v)] : List (String × Array K)).filter fun p ↦ p.1 = c).map (·.2)) =
      if c = a then [u] else if c = b then [v] else [] := by
  by_cases ha : c = a
  · subst ha
    simp [Ne.symm hab]
  · by_cases hb : c = b
    · subst hb
      simp [hab, ha]
    · simp [Ne.symm ha, Ne.symm hb, ha, hb]

/-- A row of the memory block pushes its seed `(idx, 1, m)` and pulls its finalize
`(idx, cntFin, m)`, and sends nothing on any other channel (specification §6.2 "Seed" and
"Finalize"; `layout.rs:359-382`). -/
theorem memBlock_rowMessagesOn {t : Air.Flat.Table K} (ht : t.component = ⟨memTable⟩)
    (row : Array K) {r : MemRow K} (hr : valueFromOffset MemRow 0 (t.environment row) = r)
    (c : RawChannel K) :
    rowMessagesOn t row c =
      if c.name = MemPush.name then [(toElements (⟨r.idx, 1, r.m⟩ : MemMsg K)).toArray]
      else if c.name = MemPull.name then [(toElements (⟨r.idx, r.cntFin, r.m⟩ : MemMsg K)).toArray]
      else [] := by
  rw [rowMessagesOn_eq_pairs ht,
    mem_pairs _ _ _ _ ((eval_varFromOffset_valueFromOffset MemRow 0 _).trans hr)]
  exact filter_two (by decide) _ _ _

/-- A row of the bytecode block pushes its seed `(idx, 1, opcode, op)` and pulls its finalize
`(idx, cntFin, opcode, op)`, and sends nothing on any other channel (specification §6.2, §6.4;
`layout.rs:383-395`). -/
theorem bytecodeBlock_rowMessagesOn {t : Air.Flat.Table K} (ht : t.component = ⟨bytecodeTable⟩)
    (row : Array K) {r : BytecodeRow K}
    (hr : valueFromOffset BytecodeRow 0 (t.environment row) = r) (c : RawChannel K) :
    rowMessagesOn t row c =
      if c.name = BytecodePush.name then
        [(toElements (⟨r.idx, 1, r.opcode, r.op⟩ : BytecodeMsg K)).toArray]
      else if c.name = BytecodePull.name then
        [(toElements (⟨r.idx, r.cntFin, r.opcode, r.op⟩ : BytecodeMsg K)).toArray]
      else [] := by
  rw [rowMessagesOn_eq_pairs ht,
    bytecode_pairs _ _ _ _ ((eval_varFromOffset_valueFromOffset BytecodeRow 0 _).trans hr)]
  exact filter_two (by decide) _ _ _

/-- The verifier pushes `(1, 1)` and pulls `(g^(N_prog - 1), 1)`, and sends nothing on any
other channel (specification §6.1; `layout.rs:352-358`). -/
theorem verifier_rowMessagesOn {prog : Program} {t : Air.Flat.Table K}
    (ht : t.component = ⟨leanIsaVerifier prog⟩) (row : Array K) (c : RawChannel K) :
    rowMessagesOn t row c =
      if c.name = StatePush.name then [#[1, 1]]
      else if c.name = StatePull.name then [#[prog.finalPc, 1]]
      else [] := by
  rw [rowMessagesOn_eq_pairs ht, verifier_pairs]
  exact filter_two (by decide) _ _ _

/-! ## The witness -/

/-- The messages a witness sends on a channel are its rows' messages, table by table and row
by row, the verifier's first. -/
theorem messagesOn_eq_flatMap {prog : Program} (w : EnsembleWitness (leanIsaEnsemble prog))
    (c : RawChannel K) :
    messagesOn w c =
      w.allTables.flatMap fun t ↦ t.table.flatMap fun row ↦ rowMessagesOn t row c := by
  simp only [messagesOn, EnsembleWitness.interactions, Air.Flat.Table.interactions,
    List.filter_flatMap, List.map_flatMap, rowMessagesOn]

/-- Every row of the six opcode tables of a witness sends an `OpcodeSends`, with at most nine
memory reads (`BLAKE2S`'s nine). -/
theorem exists_sendsOpcode {prog : Program} (w : EnsembleWitness (leanIsaEnsemble prog)) :
    ∀ t ∈ w.tables.take 6, ∀ row, ∃ s, SendsOpcode t row s ∧ s.mem.length ≤ 9 := by
  intro t ht row
  rw [List.mem_iff_getElem] at ht
  obtain ⟨i, hi, rfl⟩ := ht
  have hi6 : i < 6 := lt_of_lt_of_le hi (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have h8 : i < 8 := by omega
  rw [List.getElem_take]
  have hc : (w.tables[i]'(by rw [← w.same_length]; exact h8)).component =
      (leanIsaEnsemble prog).tables[i]'h8 := (w.same_circuits i h8).symm
  interval_cases i
  · exact ⟨_, xor_sendsOpcode hc row, by simp [xorSends]⟩
  · exact ⟨_, mul_sendsOpcode hc row, by simp [mulSends]⟩
  · exact ⟨_, set_sendsOpcode hc row, by simp [setSends]⟩
  · exact ⟨_, deref_sendsOpcode hc row, by simp [derefSends]⟩
  · exact ⟨_, jump_sendsOpcode hc row, by simp [jumpSends]⟩
  · exact ⟨_, blake2s_sendsOpcode hc row, by simp [blake2sSends]⟩

end LeanerVM.Arithmetization
