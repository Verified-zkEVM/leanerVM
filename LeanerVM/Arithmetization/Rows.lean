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

The messages one row of a component sends on each of the three channels in each direction, as
functions of the row's typed input `valueFromOffset Row 0 (t.environment row)`, Clean's
`Component.rowInput`: the first `size Row` cells of the raw row read as the typed row, a missing
cell `0`. The rows are arbitrary, honest or not, and nothing about the constraints is assumed.
Category A: facts about this repository's circuits, which transcribe leanVM at pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` (specification §5.1 "The bus", §6, §7;
`crates/lean_vm/src/tables.rs`, `cpu/layout.rs:352-395`), over Clean `9dd71e82`.

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

The proofs evaluate each row circuit once over a row variable `x` with `eval env x = r` and
specialize it at Clean's `varFromOffset` (`eval_varFromOffset_valueFromOffset`), reading each
interaction as its channel name, direction, multiplicity and message.

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

/-- What the bus reads of an interaction: its channel's name, its direction, its multiplicity
and its message. -/
private def quad (i : Interaction K) : String × BusDir × K × Array K :=
  (i.channel.name, i.direction, i.mult, i.msg)

/-- The active messages of the interactions on a channel name, read off their quads. -/
private theorem activeMessages_filter_eq (l : List (Interaction K)) (c : RawChannel K)
    (d : BusDir) :
    activeMessages (l.filter (·.channel.name = c.name)) d =
      ((l.map quad).filter fun p ↦ p.1 = c.name ∧ p.2.1 = d ∧ p.2.2.1 ≠ 0).map (·.2.2.2) := by
  rw [activeMessages, List.filter_filter, List.filter_map, List.map_map]
  refine congrArg (List.map _) (List.filter_congr fun i _ ↦ ?_)
  by_cases h1 : i.channel.name = c.name <;> by_cases h2 : i.direction = d <;>
    by_cases h3 : i.mult = 0 <;> simp [quad, h1, h2, h3]

/-- The quads of an opcode row's sends, in the order the tables emit them: the state pull and
push, the bytecode read, then each memory read, every one of multiplicity `1`. -/
private def OpcodeSends.quads (s : OpcodeSends) : List (String × BusDir × K × Array K) :=
  [(StateChannel.name, .pull, 1, (toElements s.pull).toArray),
    (StateChannel.name, .push, 1, (toElements s.push).toArray),
    (BytecodeChannel.name, .pull, 1, (toElements s.bc).toArray),
    (BytecodeChannel.name, .push, 1, (toElements s.bc.bump).toArray)] ++
  s.mem.flatMap fun m ↦ [(MemChannel.name, .pull, 1, (toElements m).toArray),
    (MemChannel.name, .push, 1, (toElements m.bump).toArray)]

private theorem OpcodeSends.quads_mult (s : OpcodeSends) : ∀ p ∈ s.quads, p.2.2.1 = 1 := by
  intro p hp
  simp only [OpcodeSends.quads, List.mem_append, List.mem_cons, List.mem_flatMap,
    List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl) | ⟨m, -, rfl | rfl⟩ <;> rfl

/-- Evaluating a typed message's elements is evaluating the message. -/
private theorem map_eval_toElements {M : TypeMap} [ProvableType M] (env : Environment K)
    (x : M (Expression K)) :
    (toElements x).map (Expression.eval env) = toElements (eval env x) :=
  (ProvableType.toElements_eval env x).symm

/-- A state message is the array `[pc, fp]`. -/
private theorem regs_toArray (s : Regs K) : (toElements s).toArray = #[s.pc, s.fp] :=
  Array.toList_inj.mp (by rw [Vector.toList_toArray, regs_toElements])

-- Each `*_quads` proof below writes the vector fields of the row variable as literals and
-- substitutes the typed row by its evaluation, field by field, before it evaluates the circuit:
-- a projection of an evaluated vector left under a product makes the kernel unfold
-- multiplication in `K`, and in a module the check does not return.

/-- A vector of three is a literal. -/
private theorem exists_vector_three {α : Type} (v : Vector α 3) : ∃ a b c, v = #v[a, b, c] :=
  ⟨v[0], v[1], v[2], by ext i hi; interval_cases i <;> rfl⟩

/-- A vector of two is a literal. -/
private theorem exists_vector_two {α : Type} (v : Vector α 2) : ∃ a b, v = #v[a, b] :=
  ⟨v[0], v[1], by ext i hi; interval_cases i <;> rfl⟩

/-- Substitutes the typed row by its field-by-field evaluation, the vector fields of the row
variable being literals. -/
local macro "subst_row" hx:ident : tactic => `(tactic|
  (simp only [circuit_norm, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
     at $hx:ident
   subst $hx:ident))

/-- Evaluates an opcode row circuit's quads and the sends `s` they are compared with. -/
local macro "eval_quads" circuit:ident s:ident : tactic => `(tactic|
  simp only [Operations.interactionValues, circuit_norm, $circuit:ident, instructionStep, memRead,
    bytecodeRead, AbstractInteraction.eval, map_eval_toElements, $s:ident, OpcodeSends.quads,
    quad, MemMsg.bump, BytecodeMsg.bump, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, -BitVec.reduceNeg])

/-- A row's messages on a channel in a direction, read off the quads its row circuit sends at
the row variable. -/
private theorem rowMessagesOn_eq_quads {t : Air.Flat.Table K} {c : Component K}
    (ht : t.component = c) (row : Array K) (ch : RawChannel K) (d : BusDir) :
    rowMessagesOn t row ch d =
      (((c.rowOperations.interactionValues (t.environment row)).map quad).filter
        fun p ↦ p.1 = ch.name ∧ p.2.1 = d ∧ p.2.2.1 ≠ 0).map (·.2.2.2) := by
  rw [rowMessagesOn, activeMessages_filter_eq, ht, Component.interactionsValues_eq]

/-- An opcode row whose circuit sends the quads of `s` sends `s`. -/
private theorem sendsOpcode_of_quads {t : Air.Flat.Table K} {c : Component K}
    (ht : t.component = c) (row : Array K) {s : OpcodeSends}
    (h : (c.rowOperations.interactionValues (t.environment row)).map quad = s.quads) :
    SendsOpcode t row s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [rowMessagesOn_eq_quads ht, h, OpcodeSends.quads]
    simp only [List.cons_append, List.nil_append, List.filter_cons, List.filter_flatMap,
      Channel.toRaw_name, StateChannel, MemChannel, BytecodeChannel, String.reduceEq, ne_eq,
      one_ne_zero, not_false_eq_true, and_true, decide_true, decide_false, Bool.false_eq_true,
      ite_true, ite_false, List.filter_nil, List.map_cons, regs_toArray]
    simp [List.map_flatMap, ← List.map_eq_flatMap]

/-! ## The six opcode tables -/

/-- The quads an `XOR` row circuit sends, at a row variable that evaluates to `r`. -/
private theorem xor_quads (x : Var XorRow K) (env : Environment K) (n : ℕ) (r : XorRow K)
    (hx : eval env x = r) :
    (((xorTable.main x).operations n).interactionValues env).map quad = (xorSends r).quads := by
  obtain ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ := x
  obtain ⟨a0, a1, a2, rfl⟩ := exists_vector_three vA
  obtain ⟨b0, b1, b2, rfl⟩ := exists_vector_three vB
  subst_row hx
  eval_quads xorTable xorSends

/-- Every row of an `XOR` table sends `xorSends` of its typed row. -/
theorem xor_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = xorComponent)
    (row : Array K) :
    SendsOpcode t row (xorSends (valueFromOffset XorRow 0 (t.environment row))) :=
  sendsOpcode_of_quads ht row
    (xor_quads _ _ _ _ (eval_varFromOffset_valueFromOffset XorRow 0 (t.environment row)))

/-- The quads a `MUL_NATIVE` row circuit sends, at a row variable that evaluates to `r`. -/
private theorem mul_quads (x : Var MulRow K) (env : Environment K) (n : ℕ) (r : MulRow K)
    (hx : eval env x = r) :
    (((mulTable.main x).operations n).interactionValues env).map quad = (mulSends r).quads := by
  obtain ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ := x
  obtain ⟨a0, a1, a2, rfl⟩ := exists_vector_three vA
  obtain ⟨b0, b1, b2, rfl⟩ := exists_vector_three vB
  subst_row hx
  eval_quads mulTable mulSends

/-- Every row of a `MUL_NATIVE` table sends `mulSends` of its typed row. -/
theorem mul_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = mulComponent)
    (row : Array K) :
    SendsOpcode t row (mulSends (valueFromOffset MulRow 0 (t.environment row))) :=
  sendsOpcode_of_quads ht row
    (mul_quads _ _ _ _ (eval_varFromOffset_valueFromOffset MulRow 0 (t.environment row)))

/-- The quads a `SET_CONSTANT` row circuit sends, at a row variable that evaluates to `r`. -/
private theorem set_quads (x : Var SetRow K) (env : Environment K) (n : ℕ) (r : SetRow K)
    (hx : eval env x = r) :
    (((setTable.main x).operations n).interactionValues env).map quad = (setSends r).quads := by
  obtain ⟨pc, fp, o, k, rc, rbc⟩ := x
  obtain ⟨k0, k1, k2, rfl⟩ := exists_vector_three k
  subst_row hx
  eval_quads setTable setSends

/-- Every row of a `SET_CONSTANT` table sends `setSends` of its typed row. -/
theorem set_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = setComponent)
    (row : Array K) :
    SendsOpcode t row (setSends (valueFromOffset SetRow 0 (t.environment row))) :=
  sendsOpcode_of_quads ht row
    (set_quads _ _ _ _ (eval_varFromOffset_valueFromOffset SetRow 0 (t.environment row)))

/-- The quads a `DEREF` row circuit sends, at a row variable that evaluates to `r`. -/
private theorem deref_quads (x : Var DerefRow K) (env : Environment K) (n : ℕ) (r : DerefRow K)
    (hx : eval env x = r) :
    (((derefTable.main x).operations n).interactionValues env).map quad =
      (derefSends r).quads := by
  obtain ⟨pc, fp, o1, o2, o3, fpc, ffp, p, v3, r1, r2, r3, rbc⟩ := x
  obtain ⟨a0, a1, a2, rfl⟩ := exists_vector_three v3
  subst_row hx
  eval_quads derefTable derefSends

/-- Every row of a `DEREF` table sends `derefSends` of its typed row. -/
theorem deref_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = derefComponent)
    (row : Array K) :
    SendsOpcode t row (derefSends (valueFromOffset DerefRow 0 (t.environment row))) :=
  sendsOpcode_of_quads ht row
    (deref_quads _ _ _ _ (eval_varFromOffset_valueFromOffset DerefRow 0 (t.environment row)))

/-- The quads a `JUMP` row circuit sends, at a row variable that evaluates to `r` and with the
indicator `b` at the second local witness slot. -/
private theorem jump_quads (x : Var JumpRow K) (env : Environment K) (n : ℕ) (r : JumpRow K)
    (hx : eval env x = r) :
    (((jumpTable.main x).operations n).interactionValues env).map quad =
      (jumpSends r (env.get (n + 1))).quads := by
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := x
  subst_row hx
  eval_quads jumpTable jumpSends

/-- Every row of a `JUMP` table sends `jumpSends` of its typed row and its indicator, the raw
cell after its columns and its inverse witness. -/
theorem jump_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = jumpComponent)
    (row : Array K) :
    SendsOpcode t row (jumpSends (valueFromOffset JumpRow 0 (t.environment row))
      (row[size JumpRow + 1]?.getD 0)) :=
  sendsOpcode_of_quads ht row
    (jump_quads _ _ _ _ (eval_varFromOffset_valueFromOffset JumpRow 0 (t.environment row)))

/-- The quads a `BLAKE2S` row circuit sends, at a row variable that evaluates to `r`. -/
private theorem blake2s_quads (x : Var Blake2sRow K) (env : Environment K) (n : ℕ)
    (r : Blake2sRow K) (hx : eval env x = r) :
    (((blake2sTable.main x).operations n).interactionValues env).map quad =
      (blake2sSends r).quads := by
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
  subst_row hx
  eval_quads blake2sTable blake2sSends

/-- Every row of a `BLAKE2S` table sends `blake2sSends` of its typed row. -/
theorem blake2s_sendsOpcode {t : Air.Flat.Table K} (ht : t.component = blake2sComponent)
    (row : Array K) :
    SendsOpcode t row (blake2sSends (valueFromOffset Blake2sRow 0 (t.environment row))) :=
  sendsOpcode_of_quads ht row
    (blake2s_quads _ _ _ _ (eval_varFromOffset_valueFromOffset Blake2sRow 0 (t.environment row)))

/-! ## The blocks and the verifier -/

/-- The quads a memory block row circuit sends, at a row variable that evaluates to `r`. -/
private theorem mem_quads (x : Var MemRow K) (env : Environment K) (n : ℕ) (r : MemRow K)
    (hx : eval env x = r) :
    (((memTable.main x).operations n).interactionValues env).map quad =
      [(MemChannel.name, .push, 1, (toElements (⟨r.idx, 1, r.m⟩ : MemMsg K)).toArray),
        (MemChannel.name, .pull, 1, (toElements (⟨r.idx, r.cntFin, r.m⟩ : MemMsg K)).toArray)] := by
  subst hx
  obtain ⟨idx, cntFin, m⟩ := x
  simp only [Operations.interactionValues, circuit_norm, memTable, AbstractInteraction.eval,
    map_eval_toElements, quad, -BitVec.reduceNeg]

/-- The quads a bytecode block row circuit sends, at a row variable that evaluates to `r`. -/
private theorem bytecode_quads (x : Var BytecodeRow K) (env : Environment K) (n : ℕ)
    (r : BytecodeRow K) (hx : eval env x = r) :
    (((bytecodeTable.main x).operations n).interactionValues env).map quad =
      [(BytecodeChannel.name, .push, 1,
          (toElements (⟨r.idx, 1, r.opcode, r.op⟩ : BytecodeMsg K)).toArray),
        (BytecodeChannel.name, .pull, 1,
          (toElements (⟨r.idx, r.cntFin, r.opcode, r.op⟩ : BytecodeMsg K)).toArray)] := by
  subst hx
  obtain ⟨idx, cntFin, opcode, op⟩ := x
  simp only [Operations.interactionValues, circuit_norm, bytecodeTable, AbstractInteraction.eval,
    map_eval_toElements, quad, -BitVec.reduceNeg]

/-- The quads the verifier sends, in every environment. -/
private theorem verifier_quads (prog : Program) (κ : ℕ) (env : Environment K) :
    ((leanIsaEnsemble prog κ).verifierOperations.interactionValues env).map quad =
      [(StateChannel.name, .push, 1, #[1, 1]),
        (StateChannel.name, .pull, 1, #[prog.finalPc, 1])] := by
  simp only [Operations.interactionValues, Air.Flat.Ensemble.verifierOperations,
    Verifier.Program.circuitOperations, leanIsaEnsemble, leanIsaVerifier, circuit_norm,
    AbstractInteraction.eval, map_eval_toElements, regs_toArray, quad, -BitVec.reduceNeg]

/-- Filtering a push and a pull on one channel by a channel name and a direction. -/
private theorem filter_two (a : String) (u v : Array K) (c : String) (d : BusDir) :
    ((([(a, .push, 1, u), (a, .pull, 1, v)] : List (String × BusDir × K × Array K)).filter
        fun p ↦ p.1 = c ∧ p.2.1 = d ∧ p.2.2.1 ≠ 0).map (·.2.2.2)) =
      if c = a then if d = .push then [u] else [v] else [] := by
  by_cases h : c = a
  · subst h
    cases d <;> simp
  · simp [h, Ne.symm h]

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
  rw [rowMessagesOn_eq_quads ht, show (memComponent κ).rowOperations =
      (memTable.main (varFromOffset MemRow 0)).operations (size MemRow) from rfl,
    mem_quads _ _ _ _ ((eval_varFromOffset_valueFromOffset MemRow 0 _).trans hr)]
  exact filter_two _ _ _ _ _

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
  rw [rowMessagesOn_eq_quads ht, show (bytecodeComponent prog).rowOperations =
      (bytecodeTable.main (varFromOffset BytecodeRow 0)).operations (size BytecodeRow) from rfl,
    bytecode_quads _ _ _ _ ((eval_varFromOffset_valueFromOffset BytecodeRow 0 _).trans hr)]
  exact filter_two _ _ _ _ _

/-- The verifier pushes `(1, 1)` and pulls `(g^(N_prog - 1), 1)` on the state channel, and
sends nothing on any other channel (specification §6.1; `layout.rs:352-358`). -/
theorem verifier_messagesOn {prog : Program} {κ : ℕ}
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) (c : RawChannel K) (d : BusDir) :
    verifierMessagesOn w c d =
      if c.name = StateChannel.name then
        if d = .push then [#[1, 1]] else [#[prog.finalPc, 1]]
      else [] := by
  rw [verifierMessagesOn, activeMessages_filter_eq, verifier_quads]
  exact filter_two _ _ _ _ _

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

/-- Quads that are an opcode row's sends have multiplicity `1`. -/
private theorem quads_mult_of {L : List (String × BusDir × K × Array K)} {s : OpcodeSends}
    (h : L = s.quads) : ∀ p ∈ L, p.2.2.1 = 1 := h ▸ s.quads_mult

/-- A push and a pull of multiplicity `1` have multiplicity `1`. -/
private theorem quads_mult_two {L : List (String × BusDir × K × Array K)} {a : String}
    {u v : Array K} (h : L = [(a, .push, 1, u), (a, .pull, 1, v)]) : ∀ p ∈ L, p.2.2.1 = 1 := by
  rw [h]
  simp

/-- The quads every row of every table of a witness sends have multiplicity `1`. -/
private theorem row_quads_mult {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    {t : Air.Flat.Table K} (ht : t ∈ w.tables) (row : Array K) :
    ∀ p ∈ (t.component.rowOperations.interactionValues (t.environment row)).map quad,
      p.2.2.1 = 1 := by
  obtain ⟨j, rfl⟩ := mem_tables_iff.mp ht
  rw [tableAt_component]
  have e := eval_varFromOffset_valueFromOffset (F := K)
  fin_cases j
  · exact quads_mult_of (xor_quads _ _ _ _ (e XorRow 0 _))
  · exact quads_mult_of (mul_quads _ _ _ _ (e MulRow 0 _))
  · exact quads_mult_of (set_quads _ _ _ _ (e SetRow 0 _))
  · exact quads_mult_of (deref_quads _ _ _ _ (e DerefRow 0 _))
  · exact quads_mult_of (jump_quads _ _ _ _ (e JumpRow 0 _))
  · exact quads_mult_of (blake2s_quads _ _ _ _ (e Blake2sRow 0 _))
  · exact quads_mult_two (mem_quads _ _ _ _ (e MemRow 0 _))
  · exact quads_mult_two (bytecode_quads _ _ _ _ (e BytecodeRow 0 _))

/-- Every interaction of a witness has multiplicity `1`: every component and the verifier
interact through Clean's `pull` and `push` only. -/
theorem interactions_mult_eq_one (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    ∀ i ∈ w.interactions, i.mult = 1 := by
  intro i hi
  rw [EnsembleWitness.interactions, List.mem_append] at hi
  rcases hi with hi | hi
  · have h := verifier_quads prog κ (.fromInput w.publicInput w.data)
    have hq : quad i ∈ [(StateChannel.name, (.push : BusDir), (1 : K), #[1, 1]),
        (StateChannel.name, .pull, 1, #[prog.finalPc, 1])] := h ▸ List.mem_map_of_mem hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq <;> exact congrArg (·.2.2.1) hq
  · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp hi
    obtain ⟨row, -, hi⟩ := List.mem_flatMap.mp hi
    rw [Component.interactionsValues_eq] at hi
    exact row_quads_mult ht row (quad i) (List.mem_map_of_mem hi)

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
