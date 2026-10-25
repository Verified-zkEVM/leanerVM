/-
  LeanVM.Arithmetization.Soundness.Rows

  What an arbitrary row of each of the six opcode tables sends, in the shape every table shares,
  and what the table's soundness makes of it: under the guarantees of its pulls, the row is a step
  of the machine from its pulled state to its pushed state.
-/

module

public import LeanVM.Arithmetization.Completeness.Rows
public import Statement.LeanIsa
public import LeanVM.Facts.IsaWith
public import LeanVM.Fast.CubicExt
public import LeanVM.Fast.FieldWords

@[expose] public section

/-!
# The rows of a satisfying witness

At leanVM pin `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462` and Clean pin `42fe4b26`. Specification
§7 (the six AIRs, `doc/leanvm/body/07-*`) and §6 (their bus interactions): the per-row soundness
of the six opcode tables, from the tables of `Arithmetization.Tables` and their Clean soundness
theorems; the bus is `Soundness.Bus`'s.

**The shape of a row** (`OpRow`). A raw row of a witness is an arbitrary array, read by its
component as the typed row `rowInput` (the first cells, a missing cell `0`). Whatever its cells,
the row circuit of each opcode table sends the messages `sendsOf pc fp next rbc e reads` of
`Completeness.Rows`: the state pull `(pc, fp)` and push `next`, the bytecode pull and push of the
eleven coordinates `e` at `pc`, and per memory read a pull of `(addr, count, v)` and a push of
`(addr, g·count, v)`, at most twenty-six reads (`KECCAK`). The memory and bytecode pairs need nothing
more of the rows than this shape (`Soundness.MemChannel`, `Soundness.BytecodeChannel`).

**The step** (also `OpRow`). Under the table's `Assumptions` (the permutation, for `KECCAK`), its
constraints (the `JUMP` residuals), and the guarantees of its pulls (that the memory reads are the
image's words and the bytecode entry decodes, which `Soundness.MemChannel` and
`Soundness.BytecodeChannel` derive from the bus), Clean's instantiated soundness theorem
(`Component.weakSoundness`) gives the table's `Spec`: the row refines the table's relation, so some
instruction `ins` with `entry ins = e` executes from `(pc, fp)` to `next` (`execute`), and
to the fall-through `(g·pc, fp)` unless it is a `JUMP`. The pushed successor is the table's output,
which for `JUMP` reads the indicator, the row's second local witness (`jump_output_gen`).

**The guarantees** (`ChannelOk`). Of the six channels only the memory pull and the bytecode pull
carry a guarantee; every interaction a table emits is on one of the six (`*_channelOk`), so the
guarantees of a row are those of its memory and bytecode pulls.

**Without the permutation** (`OpRow`'s last clause). Under its constraints and the guarantees
alone a row is a step of the reduction-blind semantics `keccakFree` (`Statement.LeanIsa`), whose
`KECCAK` asks only canonical cells with the written cells' free limb zero: a `KECCAK` row is bound
to the image by the table's circuit without its assumption (`keccakTableFree`), and its cells are
cells of lanes (`keccak_free_exec`); every other table assumes nothing, and a deployed step is a
reduction-blind one (`executeWithB_free_of_executeWith`).

## Wrong readings excluded

* A row is not assumed to be a typed row written by an honest prover: the shape holds for every
  array, the step only under the guarantees, which the bus supplies.
* The table does not know which instruction the program holds at `pc`: `e = entry ins` names the
  instruction the row's own columns encode, and that it is the program's is the bytecode pair's
  (`Soundness.BytecodeChannel`).
* The `JUMP` successor is not read from the row's columns alone: it is the output, a function of
  the indicator, forced by the residuals (`flags_sound`) inside the table's soundness.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component)

/-! ## The shape of a row -/

/-- The parameters of what an opcode-table row sends (`sendsOf`): the pulled state, the pushed
successor, the bytecode count and coordinates, and the memory reads. -/
structure RowRec where
  /-- The pulled program counter. -/
  pc : K
  /-- The pulled frame pointer. -/
  fp : K
  /-- The pushed successor. -/
  next : Regs K
  /-- The bytecode read count. -/
  rbc : K
  /-- The bytecode coordinates `(opcode, op₁, …, op₁₀)`. -/
  e : Vector K 11
  /-- The memory reads `(addr, count, limbs)`. -/
  reads : List (K × K × Vector K 3)

/-- A record exists. -/
instance : Inhabited RowRec := ⟨⟨0, 0, ⟨0, 0⟩, 0, 0, []⟩⟩

/-- What a row with these parameters sends. -/
def RowRec.sends (x : RowRec) : List (String × Array K) :=
  sendsOf x.pc x.fp x.next x.rbc x.e x.reads

/-- The pulled state of a record. -/
def RowRec.src (x : RowRec) : Regs K := ⟨x.pc, x.fp⟩

/-- A component's row in the environment `env` has the shape of an opcode-table row, with at
most twenty-six memory reads, and under the table's assumptions, constraints and pull guarantees it is
a step: an instruction encoded by its bytecode coordinates executes from its pulled state to its
pushed state over the image the data names, to the fall-through unless it is a `JUMP`. Without
the assumptions (the permutation, for `KECCAK`) it is a step under the reduction-blind semantics
`keccakFree` (`Statement.LeanIsa`). -/
def OpRow (c : Component K) (env : Environment K) : Prop :=
  ∃ x : RowRec, rowSends c env = x.sends ∧ x.reads.length ≤ 26 ∧
    (c.Assumptions env → c.operations.ConstraintsHold env → c.operations.FullGuarantees env →
      ∃ ins, x.e = entry ins ∧ execute (imageOf env.data).2 x.src ins = some x.next ∧
        (ins.opcode ≠ .jump → x.next = ⟨g * x.pc, x.fp⟩)) ∧
    (c.operations.ConstraintsHold env → c.operations.FullGuarantees env →
      ∃ ins, x.e = entry ins ∧
        executeWithB keccakFree (imageOf env.data).2.read x.src ins = some x.next ∧
        (ins.opcode ≠ .jump → x.next = ⟨g * x.pc, x.fp⟩))

/-- **A deployed step is a reduction-blind step**: the cells Keccak-f writes are canonical with
their free limb zero. -/
theorem executeWithB_free_of_executeWith {read : K → Option E} {r next : Regs K} {ins : Instr}
    (h : executeWith read r ins = some next) : executeWithB keccakFree read r ins = some next := by
  cases ins with
  | keccak om otail ob8 ocap oout inOdd outOdd =>
    simp only [executeWith, executeWithB, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨input, hin, output, hout, u, hu, hnext⟩ := h
    refine ⟨input, hin, output, hout, (), ?_, hnext⟩
    have hc := canonicalKeccak_of_keccakCells (guard_eq_some hu)
    unfold guard
    simp only [keccakFree, hc, ↓reduceIte]
    rfl
  | _ => exact h

/-- A row of a table whose assumptions hold is a reduction-blind step where it is a step. -/
theorem opRow_of_assumptions {c : Component K} {env : Environment K} (hA : c.Assumptions env)
    (h : ∃ x : RowRec, rowSends c env = x.sends ∧ x.reads.length ≤ 26 ∧
      (c.Assumptions env → c.operations.ConstraintsHold env → c.operations.FullGuarantees env →
        ∃ ins, x.e = entry ins ∧ execute (imageOf env.data).2 x.src ins = some x.next ∧
          (ins.opcode ≠ .jump → x.next = ⟨g * x.pc, x.fp⟩))) :
    OpRow c env := by
  obtain ⟨x, hs, hl, hd⟩ := h
  exact ⟨x, hs, hl, hd, fun hc hg ↦ (hd hA hc hg).imp fun _ h ↦
    ⟨h.1, executeWithB_free_of_executeWith h.2.1, h.2.2⟩⟩

/-! ## The six tables -/

/-- An `XOR` row has the shape and, under the guarantees, steps. -/
theorem xor_opRow (env : Environment K) : OpRow ⟨xorTable⟩ env := by
  set r := (⟨xorTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset XorRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine opRow_of_assumptions trivial
    ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc, entry (.xor r.oA r.oB r.oC),
    [(r.fp * r.oA, r.rA, r.vA), (r.fp * r.oB, r.rB, r.vB),
     (r.fp * r.oC, r.rC, #v[r.vA[0] + r.vB[0], r.vA[1] + r.vB[1], r.vA[2] + r.vB[2]])]⟩,
    ?_, by simp, ?_⟩
  · rw [rowSends_mk, xor_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf, entry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : XorRefines (imageOf env.data).2 r ((⟨xorTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨-, -, hnext⟩ := (xor_refines_iff _ _ _).mp hs'
    refine ⟨.xor r.oA r.oB r.oC, rfl, ?_, fun _ ↦ rfl⟩
    rw [← show ((⟨xorTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `SET_CONSTANT` row has the shape and, under the guarantees, steps. -/
theorem set_opRow (env : Environment K) : OpRow ⟨setTable⟩ env := by
  set r := (⟨setTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset SetRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine opRow_of_assumptions trivial ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc,
    #v[Opcode.setConstant.code, r.o, r.k[0], r.k[1], r.k[2], 0, 0, 0, 0, 0, 0],
    [(r.fp * r.o, r.r, r.k)]⟩, ?_, by simp, ?_⟩
  · rw [rowSends_mk, set_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : SetRefines (imageOf env.data).2 r ((⟨setTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨-, hnext⟩ := (set_refines_iff _ _ _).mp hs'
    refine ⟨.setConstant r.o (E.ofLimbs r.k[0] r.k[1] r.k[2]), by simp [entry, limb_ofLimbs],
      ?_, fun _ ↦ rfl⟩
    rw [← show ((⟨setTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `MUL_NATIVE` row has the shape and, under the guarantees, steps. -/
theorem mul_opRow (env : Environment K) : OpRow ⟨mulTable⟩ env := by
  set r := (⟨mulTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset MulRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine opRow_of_assumptions trivial
    ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc, entry (.mulNative r.oA r.oB r.oC),
    [(r.fp * r.oA, r.rA, r.vA), (r.fp * r.oB, r.rB, r.vB),
     (r.fp * r.oC, r.rC, #v[r.vA[0] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1],
          r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1] +
            r.vA[2] * r.vB[2],
          r.vA[0] * r.vB[2] + r.vA[1] * r.vB[1] + r.vA[2] * r.vB[0] + r.vA[2] * r.vB[2]])]⟩,
    ?_, by simp, ?_⟩
  · rw [rowSends_mk, mul_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf, entry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : MulRefines (imageOf env.data).2 r ((⟨mulTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨-, -, hnext⟩ := (mul_refines_iff _ _ _).mp hs'
    refine ⟨.mulNative r.oA r.oB r.oC, rfl, ?_, fun _ ↦ rfl⟩
    rw [← show ((⟨mulTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `DEREF` row has the shape and, under the guarantees, steps: the mode is the one its flags
name. -/
theorem deref_opRow (env : Environment K) : OpRow ⟨derefTable⟩ env := by
  set r := (⟨derefTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset DerefRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine opRow_of_assumptions trivial ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc,
    #v[Opcode.deref.code, r.o1, r.o2, r.o3, r.fpc, r.ffp, 0, 0, 0, 0, 0],
    [(r.fp * r.o1, r.r1, #v[r.p, 0, 0]),
     (r.p * r.o2, r.r2, #v[(1 + r.fpc + r.ffp) * r.v3[0] + r.fpc * (g ^ 2 * r.pc) + r.ffp * r.fp,
          (1 + r.fpc + r.ffp) * r.v3[1], (1 + r.fpc + r.ffp) * r.v3[2]]),
     (r.fp * r.o3, r.r3, r.v3)]⟩,
    ?_, by simp, ?_⟩
  · rw [rowSends_mk, deref_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : DerefRefines (imageOf env.data).2 r
      ((⟨derefTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨mode, hb, -, hnext⟩ := (deref_refines_iff _ _ _).mp hs'
    obtain ⟨mode', hb', hexec⟩ := hs'
    have hflags := hb.flags_eq
    have hm : mode' = mode := by
      have h1 := derefMode?_flags mode
      have h2 := derefMode?_flags mode'
      rw [hflags] at h1
      rw [hb'.flags_eq] at h2
      exact Option.some.inj (h2.symm.trans h1)
    subst hm
    refine ⟨.deref r.o1 r.o2 r.o3 mode', ?_, ?_, fun _ ↦ rfl⟩
    · simp [entry, hflags]
    · rw [← show ((⟨derefTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
      exact hexec

set_option maxHeartbeats 16000000 in
/-- **The `KECCAK` table without its assumption**: the same row circuit, sound for the flags, the
bindings and the fall-through alone, whatever the output lanes hold (the reduction-blind reading
of a row). -/
def keccakTableFree : GeneralFormalCircuit K KeccakRow Regs :=
  { keccakTable with
    Assumptions := fun _ _ ↦ True
    Spec := fun r next data ↦ (∃ inOdd outOdd : Bool, r.oddIn = flagK inOdd ∧
      r.oddOut = flagK outOdd ∧ KeccakBindings (imageOf data).2 r inOdd outOdd) ∧
      next = Regs.next ⟨r.pc, r.fp⟩
    soundness := by
      circuit_proof_start [keccakTable, StatePull, StatePush, MemPull, MemPush, BytecodePull,
        BytecodePush, memRead, bytecodeRead]
      obtain ⟨⟨ins, hdec⟩, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩ := h_holds
      obtain ⟨_, _, hom, _, _, _, _, hoi, hoo, _, hlin, hlout, _, _⟩ := h_input
      subst hom hlin hlout
      rw [keccak_tuple] at hdec
      obtain ⟨inOdd, outOdd, hfi, hfo⟩ := keccak_flags_of_decode rfl hdec
      simp only [hfi] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      simp only [hfo] at h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
      refine ⟨⟨inOdd, outOdd, hfi, hfo, ⟨fun c ↦ ?_, fun c ↦ ?_⟩⟩, rfl⟩
      · fin_cases c
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, KeccakRow.oms, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h0 ⊢ <;> exact h0
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, KeccakRow.oms, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h1 ⊢ <;> exact h1
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, KeccakRow.oms, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h2 ⊢ <;> exact h2
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, KeccakRow.oms, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h3 ⊢ <;> exact h3
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, pow_zero, one_mul] at h4 ⊢ <;> exact h4
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul, pow_one] at h5 ⊢ <;> exact h5
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h6 ⊢ <;> exact h6
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h7 ⊢ <;> exact h7
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h8 ⊢ <;> exact h8
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, Vector.getElem_map, pow_zero, one_mul] at h9 ⊢ <;> exact h9
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, Vector.getElem_map, pow_one] at h10 ⊢ <;> exact h10
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, Vector.getElem_map] at h11 ⊢ <;> exact h11
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, Vector.getElem_map] at h12 ⊢ <;> exact h12
      · fin_cases c
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, pow_zero, one_mul] at h13 ⊢ <;> exact h13
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul, pow_one] at h14 ⊢ <;> exact h14
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h15 ⊢ <;> exact h15
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h16 ⊢ <;> exact h16
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h17 ⊢ <;> exact h17
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h18 ⊢ <;> exact h18
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h19 ⊢ <;> exact h19
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h20 ⊢ <;> exact h20
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h21 ⊢ <;> exact h21
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h22 ⊢ <;> exact h22
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h23 ⊢ <;> exact h23
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h24 ⊢ <;> exact h24
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h25 ⊢ <;> exact h25 }

/-- The cells of lanes in a layout satisfy the reduction-blind check: canonical, the written
cells' free limb zero. -/
theorem canonicalKeccak_laneCells (L L' : Fin 25 → K) (inOdd outOdd : Bool) (free : K) :
    CanonicalKeccak (laneCells L inOdd free) inOdd (laneCells L' outOdd 0) outOdd := by
  refine ⟨fun c ↦ ?_, fun c ↦ ?_, ?_⟩
  · show (E.ofLimbs _ _ 0).limb 2 = 0
    rw [limb_ofLimbs]; rfl
  · show (E.ofLimbs _ _ 0).limb 2 = 0
    rw [limb_ofLimbs]; rfl
  · cases outOdd <;> simp [FreeLimbZero, laneCells, cellLanes, laneLimb, limb_ofLimbs]

/-- A bound `KECCAK` row executes under the reduction-blind semantics. -/
theorem keccak_free_exec {κ : ℕ} {mem : MemImage κ} {r : KeccakRow K} {inOdd outOdd : Bool}
    (h : KeccakBindings mem r inOdd outOdd) :
    executeWithB keccakFree mem.read ⟨r.pc, r.fp⟩
      (.keccak r.oms r.otail r.ob8 r.ocap r.oout inOdd outOdd) =
        some (Regs.next ⟨r.pc, r.fp⟩) := by
  have hin := (readCells_eq_some_iff mem.read r.fp (keccakInOffset r.oms r.otail r.ob8 r.ocap)
    (laneCells r.inLanes inOdd r.free)).mpr h.in_eq
  have hout := (readCells_eq_some_iff mem.read r.fp (fun c ↦ g ^ c.val * r.oout)
    (laneCells r.outLanes outOdd 0)).mpr h.out_eq
  simp only [executeWithB, keccakFree, hin, hout, Option.bind_eq_bind, Option.bind_some]
  unfold guard
  simp only [canonicalKeccak_laneCells, ↓reduceIte]
  rfl

/-- A `KECCAK` row has the shape and, under the permutation and the guarantees, steps; without the
permutation it is a reduction-blind step. -/
theorem keccak_opRow (env : Environment K) : OpRow ⟨keccakTable⟩ env := by
  set r := (⟨keccakTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset KeccakRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc,
    #v[Opcode.keccak.code, r.om[0], r.om[1], r.om[2], r.om[3], r.otail, r.ob8, r.ocap, r.oout,
      r.oddIn, r.oddOut],
    [(r.fp * r.om[0], r.cnt[0], #v[r.lin[0] + r.oddIn * r.lin[0] + r.oddIn * r.free, r.lin[1] + r.oddIn * r.lin[1] + r.oddIn * r.lin[0], 0]),
     (r.fp * r.om[1], r.cnt[1], #v[r.lin[2] + r.oddIn * r.lin[2] + r.oddIn * r.lin[1], r.lin[3] + r.oddIn * r.lin[3] + r.oddIn * r.lin[2], 0]),
     (r.fp * r.om[2], r.cnt[2], #v[r.lin[4] + r.oddIn * r.lin[4] + r.oddIn * r.lin[3], r.lin[5] + r.oddIn * r.lin[5] + r.oddIn * r.lin[4], 0]),
     (r.fp * r.om[3], r.cnt[3], #v[r.lin[6] + r.oddIn * r.lin[6] + r.oddIn * r.lin[5], r.lin[7] + r.oddIn * r.lin[7] + r.oddIn * r.lin[6], 0]),
     (r.fp * (g ^ 0 * r.otail), r.cnt[4], #v[r.lin[8] + r.oddIn * r.lin[8] + r.oddIn * r.lin[7], r.lin[9] + r.oddIn * r.lin[9] + r.oddIn * r.lin[8], 0]),
     (r.fp * (g ^ 1 * r.otail), r.cnt[5], #v[r.lin[10] + r.oddIn * r.lin[10] + r.oddIn * r.lin[9], r.lin[11] + r.oddIn * r.lin[11] + r.oddIn * r.lin[10], 0]),
     (r.fp * (g ^ 2 * r.otail), r.cnt[6], #v[r.lin[12] + r.oddIn * r.lin[12] + r.oddIn * r.lin[11], r.lin[13] + r.oddIn * r.lin[13] + r.oddIn * r.lin[12], 0]),
     (r.fp * (g ^ 3 * r.otail), r.cnt[7], #v[r.lin[14] + r.oddIn * r.lin[14] + r.oddIn * r.lin[13], r.lin[15] + r.oddIn * r.lin[15] + r.oddIn * r.lin[14], 0]),
     (r.fp * r.ob8, r.cnt[8], #v[r.lin[16] + r.oddIn * r.lin[16] + r.oddIn * r.lin[15], r.free + r.oddIn * r.free + r.oddIn * r.lin[16], 0]),
     (r.fp * (g ^ 0 * r.ocap), r.cnt[9], #v[r.lin[17], r.lin[18], 0]),
     (r.fp * (g ^ 1 * r.ocap), r.cnt[10], #v[r.lin[19], r.lin[20], 0]),
     (r.fp * (g ^ 2 * r.ocap), r.cnt[11], #v[r.lin[21], r.lin[22], 0]),
     (r.fp * (g ^ 3 * r.ocap), r.cnt[12], #v[r.lin[23], r.lin[24], 0]),
     (r.fp * (g ^ 0 * r.oout), r.cnt[13], #v[r.lout[0] + r.oddOut * r.lout[0], r.lout[1] + r.oddOut * r.lout[1] + r.oddOut * r.lout[0], 0]),
     (r.fp * (g ^ 1 * r.oout), r.cnt[14], #v[r.lout[2] + r.oddOut * r.lout[2] + r.oddOut * r.lout[1], r.lout[3] + r.oddOut * r.lout[3] + r.oddOut * r.lout[2], 0]),
     (r.fp * (g ^ 2 * r.oout), r.cnt[15], #v[r.lout[4] + r.oddOut * r.lout[4] + r.oddOut * r.lout[3], r.lout[5] + r.oddOut * r.lout[5] + r.oddOut * r.lout[4], 0]),
     (r.fp * (g ^ 3 * r.oout), r.cnt[16], #v[r.lout[6] + r.oddOut * r.lout[6] + r.oddOut * r.lout[5], r.lout[7] + r.oddOut * r.lout[7] + r.oddOut * r.lout[6], 0]),
     (r.fp * (g ^ 4 * r.oout), r.cnt[17], #v[r.lout[8] + r.oddOut * r.lout[8] + r.oddOut * r.lout[7], r.lout[9] + r.oddOut * r.lout[9] + r.oddOut * r.lout[8], 0]),
     (r.fp * (g ^ 5 * r.oout), r.cnt[18], #v[r.lout[10] + r.oddOut * r.lout[10] + r.oddOut * r.lout[9], r.lout[11] + r.oddOut * r.lout[11] + r.oddOut * r.lout[10], 0]),
     (r.fp * (g ^ 6 * r.oout), r.cnt[19], #v[r.lout[12] + r.oddOut * r.lout[12] + r.oddOut * r.lout[11], r.lout[13] + r.oddOut * r.lout[13] + r.oddOut * r.lout[12], 0]),
     (r.fp * (g ^ 7 * r.oout), r.cnt[20], #v[r.lout[14] + r.oddOut * r.lout[14] + r.oddOut * r.lout[13], r.lout[15] + r.oddOut * r.lout[15] + r.oddOut * r.lout[14], 0]),
     (r.fp * (g ^ 8 * r.oout), r.cnt[21], #v[r.lout[16] + r.oddOut * r.lout[16] + r.oddOut * r.lout[15], r.oddOut * r.lout[16], 0]),
     (r.fp * (g ^ 9 * r.oout), r.cnt[22], #v[r.lout[17], r.lout[18], 0]),
     (r.fp * (g ^ 10 * r.oout), r.cnt[23], #v[r.lout[19], r.lout[20], 0]),
     (r.fp * (g ^ 11 * r.oout), r.cnt[24], #v[r.lout[21], r.lout[22], 0]),
     (r.fp * (g ^ 12 * r.oout), r.cnt[25], #v[r.lout[23], r.lout[24], 0])]⟩, ?_, by simp, ?_, ?_⟩
  · rw [rowSends_mk, keccak_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : KeccakRefines (imageOf env.data).2 r
      ((⟨keccakTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨⟨inOdd, outOdd, hfi, hfo, -⟩, -, hnext⟩ := (keccak_refines_iff _ _ _).mp hs'
    obtain ⟨i, o, hi, ho, -, hexec⟩ := hs'
    have hi' : i = inOdd := by
      have := congrArg flag? (hi.symm.trans hfi); simpa [flag?_flagK] using this
    have ho' : o = outOdd := by
      have := congrArg flag? (ho.symm.trans hfo); simpa [flag?_flagK] using this
    subst hi' ho'
    refine ⟨.keccak r.oms r.otail r.ob8 r.ocap r.oout i o, ?_, ?_, fun _ ↦ rfl⟩
    · simp [entry, hfi, hfo, KeccakRow.oms]
    · rw [← show ((⟨keccakTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
      exact hexec
  · intro hc hg
    obtain ⟨⟨⟨inOdd, outOdd, hfi, hfo, hb⟩, -⟩, -⟩ :=
      Component.weakSoundness (component := ⟨keccakTableFree⟩) trivial hc hg
    have hfi' : r.oddIn = flagK inOdd := hfi
    have hfo' : r.oddOut = flagK outOdd := hfo
    have hb' : KeccakBindings (imageOf env.data).2 r inOdd outOdd := hb
    exact ⟨.keccak r.oms r.otail r.ob8 r.ocap r.oout inOdd outOdd,
      by simp [entry, hfi', hfo', KeccakRow.oms], keccak_free_exec hb', fun _ ↦ rfl⟩

/-- The output of the `JUMP` row circuit at a row variable that evaluates to `r`: the successor
selected by the indicator `b`, the local witness at slot `n + 1`. -/
theorem jump_output_gen (x : Var JumpRow K) (env : Environment K) (n : ℕ) (r : JumpRow K)
    (hx : eval env x = r) (b : K) (hb : env.get (n + 1) = b) :
    eval env ((jumpTable.main x).output n) =
      (⟨b * r.vpc + b * (g * r.pc) + g * r.pc, b * r.vfp + b * r.fp + r.fp⟩ : Regs K) := by
  subst hx
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := x
  dsimp only [jumpTable]
  simp only [circuit_norm, memRead, bytecodeRead, hb, -BitVec.reduceNeg]

/-- A `JUMP` row has the shape, its pushed successor the table's output, and under the residuals
and the guarantees steps. -/
theorem jump_opRow (env : Environment K) : OpRow ⟨jumpTable⟩ env := by
  set r := (⟨jumpTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset JumpRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine opRow_of_assumptions trivial
    ⟨⟨r.pc, r.fp, (⟨jumpTable⟩ : Component K).rowOutput env, r.rbc,
    entry (.jump r.oc r.od r.of),
    [(r.fp * r.oc, r.rc, #v[r.vcond, 0, 0]), (r.fp * r.od, r.rd, #v[r.vpc, 0, 0]),
     (r.fp * r.of, r.rf, #v[r.vfp, 0, 0])]⟩, ?_, by simp, ?_⟩
  · have ho : (⟨jumpTable⟩ : Component K).rowOutput env = _ :=
      jump_output_gen _ env (size JumpRow) r hx _ rfl
    rw [rowSends_mk, jump_sends_gen _ _ _ _ hx _ rfl, ho]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf, entry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : JumpRefines (imageOf env.data).2 r
      ((⟨jumpTable⟩ : Component K).rowOutput env) := hs
    exact ⟨_, rfl, hs'.exec_eq, fun h ↦ absurd rfl h⟩

/-! ## The guarantees of a row -/

/-- A channel whose guarantee a row may need: the memory pull, the bytecode pull, or a channel
guaranteeing nothing. -/
def ChannelOk (ch : RawChannel K) : Prop :=
  ch = MemPull.toRaw ∨ ch = BytecodePull.toRaw ∨ ∀ mult msg data, ch.Guarantees mult msg data

-- Each of the six channels is `ChannelOk`: the two lookup pulls by name, the others since their
-- guarantee is `True` at every multiplicity.
private theorem channelOk_memPull : ChannelOk MemPull.toRaw := Or.inl rfl
private theorem channelOk_bytecodePull : ChannelOk BytecodePull.toRaw := Or.inr (Or.inl rfl)
private theorem channelOk_statePull : ChannelOk StatePull.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
private theorem channelOk_statePush : ChannelOk StatePush.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
private theorem channelOk_memPush : ChannelOk MemPush.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
private theorem channelOk_bytecodePush : ChannelOk BytecodePush.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)

/-- Every interaction of the `XOR` table is on one of the six channels. -/
theorem xor_channelOk : ∀ a ∈ (⟨xorTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, xorTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `MUL_NATIVE` table is on one of the six channels. -/
theorem mul_channelOk : ∀ a ∈ (⟨mulTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, mulTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `SET_CONSTANT` table is on one of the six channels. -/
theorem set_channelOk : ∀ a ∈ (⟨setTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, setTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `DEREF` table is on one of the six channels. -/
theorem deref_channelOk : ∀ a ∈ (⟨derefTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, derefTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `JUMP` table is on one of the six channels. -/
theorem jump_channelOk : ∀ a ∈ (⟨jumpTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  dsimp only [Component.rowOperations_mk, jumpTable]
  simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

set_option maxHeartbeats 16000000 in
/-- Every interaction of the `KECCAK` table is on one of the six channels. -/
theorem keccak_channelOk : ∀ a ∈ (⟨keccakTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, keccakTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-! ## The opcode tables of a witness -/

variable {prog : Program}

/-- Each of the first six tables of a witness has rows of the opcode-table shape, and every
interaction it emits is on one of the six channels. -/
theorem tableAt_opRow (w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog)) (j : Fin 8)
    (hj : (j : ℕ) < 6) :
    (∀ env, OpRow (tableAt w j).component env) ∧
      ∀ a ∈ (tableAt w j).component.operations.interactions, ChannelOk a.channel := by
  rw [tableAt_component]
  fin_cases j
  · exact ⟨xor_opRow, xor_channelOk⟩
  · exact ⟨mul_opRow, mul_channelOk⟩
  · exact ⟨set_opRow, set_channelOk⟩
  · exact ⟨deref_opRow, deref_channelOk⟩
  · exact ⟨jump_opRow, jump_channelOk⟩
  · exact ⟨keccak_opRow, keccak_channelOk⟩
  · exact absurd hj (by decide)
  · exact absurd hj (by decide)

end LeanVM.Arithmetization
