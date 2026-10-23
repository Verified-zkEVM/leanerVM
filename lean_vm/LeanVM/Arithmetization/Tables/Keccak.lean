/-
  LeanVM.Arithmetization.Tables.Keccak

  The `KECCAK` table: one Clean component per row, sound and complete for the relation the row
  refines, its bindings to an image together with `execute` of the instruction it names, under
  the named assumption that the Keccak reduction proves the permutation on the row's lanes.
-/

module

public import LeanVM.Arithmetization.Tables.Basic
public import LeanVM.Semantics.KeccakCells
public import Clean.Circuit.Formal
public import Clean.Utils.Tactics.CircuitProofStart
public import Mathlib.Algebra.CharP.Two

@[expose] public section

/-!
# The `KECCAK` table

At leanVM pin `3375f7a137c50b803f3416f6466b5d4e0719708a` and Clean pin `42fe4b26`. The columns
are `KECCAK_COLUMNS` (`verifier.py:925-934`; `crates/leanvm_core/src/tables.rs`, the `KECCAK`
table) and the flushes `_flushes_keccak` (`verifier.py:888-916`), matching specification §7
(`doc/leanvm/body/07-instruction-tables.tex`). There is no table constraint: the permutation is
proved by the Keccak reduction (`verify_keccak`) on the input lanes committed to `q_keccak` and
the output lanes the table's claims hand it.

**The row** `KeccakRow` is the column list: `pc, fp`; the operands `o_m₀, …, o_m₃` (`om`),
`o_tail, o_b8, o_cap, o_out`; the two layout flags `odd_in, odd_out`; the read limb holding no
lane (`free`); the 25 input lanes (`lin`) and the 25 output lanes (`lout`); one memory count per
cell, the thirteen read then the thirteen written (`cnt`); the bytecode count `r_bc`. A cell's
limb holding lane `a` in the even layout and `b` in the odd one is `a + flag·a + flag·b` (the
Python's `_layout_limb`): `a` at `flag = 0`, `b` at `flag = 1`; every cell's top limb is a literal
zero.

**The relation.** `KeccakBindings mem r inOdd outOdd` binds the row to an image: the thirteen
cells read hold the input lanes in the layout `inOdd` (`laneCells`, the free limb the column
`free`), the thirteen written hold the output lanes in the layout `outOdd` (the free limb zero).
`KeccakRefines mem r next` says the row's flags are the bits `inOdd`, `outOdd`, the row is bound,
and the machine executes `KECCAK` with the row's operands and these layouts to `next`;
`keccak_refines_iff` expands it: the flags and the bindings, `KeccakRelation r` (the output lanes
are Keccak-f[1600] of the input lanes), and the successor `(g·pc, fp)`.

**The boundary.** `KeccakRelation r` is the table's `Assumptions` field: the component proves the
memory binding, and the Keccak reduction discharges the permutation for the composed system.
The layout flags are read from the bytecode guarantee (the pulled entry decodes, so they are `0`
or `1`): the one use the table makes of it.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-! ## The row -/

/-- The `KECCAK` columns, in the order of `KECCAK_COLUMNS` (`verifier.py:925-934`). -/
structure KeccakRow (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operands `o_m₀, …, o_m₃` of the four addressed cells. -/
  om : Vector F 4
  /-- The operand `o_tail`: four consecutive cells. -/
  otail : F
  /-- The operand `o_b8`. -/
  ob8 : F
  /-- The operand `o_cap`: the four capacity cells. -/
  ocap : F
  /-- The operand `o_out`: the thirteen written cells. -/
  oout : F
  /-- The layout flag of the cells read. -/
  oddIn : F
  /-- The layout flag of the cells written. -/
  oddOut : F
  /-- The read limb that holds no lane. -/
  free : F
  /-- The input state's lanes. -/
  lin : Vector F 25
  /-- The output state's lanes. -/
  lout : Vector F 25
  /-- The read counts: the thirteen cells read, then the thirteen written. -/
  cnt : Vector F 26
  /-- The read count of the bytecode entry at `pc`. -/
  rbc : F
  deriving ProvableStruct

/-- The input lanes of a row. -/
def KeccakRow.inLanes (r : KeccakRow K) : Fin 25 → K := fun l ↦ r.lin[l]

/-- The output lanes of a row. -/
def KeccakRow.outLanes (r : KeccakRow K) : Fin 25 → K := fun l ↦ r.lout[l]

/-- The four addressed operands of a row. -/
def KeccakRow.oms (r : KeccakRow K) : Fin 4 → K := fun i ↦ r.om[i]

/-- The permutation on a row's lanes, as the Keccak reduction proves it: the output lanes are
Keccak-f[1600] of the input lanes. The named assumption of the table. -/
def KeccakRelation (r : KeccakRow K) : Prop :=
  r.outLanes = stateLanes (keccakF (laneState r.inLanes))

/-! ## The relation -/

/-- The row's bindings to an image, in the layouts `inOdd`, `outOdd`: the cells read hold the
input lanes, the cells written the output lanes. -/
structure KeccakBindings {κ : ℕ} (mem : MemImage κ) (r : KeccakRow K) (inOdd outOdd : Bool) :
    Prop where
  /-- Cell `c` read holds the input lanes' cell `c` in the layout `inOdd`. -/
  in_eq : ∀ c : Fin 13, mem.read (r.fp * keccakInOffset r.oms r.otail r.ob8 r.ocap c) =
    some (laneCells r.inLanes inOdd r.free c)
  /-- Cell `c` written holds the output lanes' cell `c` in the layout `outOdd`. -/
  out_eq : ∀ c : Fin 13, mem.read (r.fp * (g ^ c.val * r.oout)) =
    some (laneCells r.outLanes outOdd 0 c)

/-- The relation a `KECCAK` row refines: its flags are the layouts `inOdd`, `outOdd`, it is bound
to the image, and from its registers the machine executes the instruction it names to `next`. -/
def KeccakRefines {κ : ℕ} (mem : MemImage κ) (r : KeccakRow K) (next : Regs K) : Prop :=
  ∃ inOdd outOdd : Bool, r.oddIn = flagK inOdd ∧ r.oddOut = flagK outOdd ∧
    KeccakBindings mem r inOdd outOdd ∧
    execute mem ⟨r.pc, r.fp⟩ (.keccak r.oms r.otail r.ob8 r.ocap r.oout inOdd outOdd) = some next

/-- `KeccakRefines`, expanded: the flags and the bindings, the permutation on the lanes, and the
successor `(g·pc, fp)`. -/
theorem keccak_refines_iff {κ : ℕ} (mem : MemImage κ) (r : KeccakRow K) (next : Regs K) :
    KeccakRefines mem r next ↔
      (∃ inOdd outOdd : Bool, r.oddIn = flagK inOdd ∧ r.oddOut = flagK outOdd ∧
        KeccakBindings mem r inOdd outOdd) ∧
      KeccakRelation r ∧ next = Regs.next ⟨r.pc, r.fp⟩ := by
  constructor
  · rintro ⟨inOdd, outOdd, hi, ho, hb, hexec⟩
    obtain ⟨input, output, hin, hout, hcells, hnext⟩ :=
      (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _).mp hexec
    have hinput : input = laneCells r.inLanes inOdd r.free := by
      funext c; exact Option.some.inj ((hin c).symm.trans (hb.in_eq c))
    have houtput : output = laneCells r.outLanes outOdd 0 := by
      funext c; exact Option.some.inj ((hout c).symm.trans (hb.out_eq c))
    refine ⟨⟨inOdd, outOdd, hi, ho, hb⟩, ?_, hnext⟩
    have h2 := hcells.2
    rw [hinput, houtput, stateOfCells_laneCells] at h2
    have h3 : laneCells r.outLanes outOdd 0 =
        laneCells (stateLanes (keccakF (laneState r.inLanes))) outOdd 0 := by
      funext c; rw [h2 c, cellsOfState_eq_laneCells]
    exact laneCells_eq_iff.mp h3
  · rintro ⟨⟨inOdd, outOdd, hi, ho, hb⟩, hrel, rfl⟩
    refine ⟨inOdd, outOdd, hi, ho, hb, ?_⟩
    refine (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _).mpr
      ⟨laneCells r.inLanes inOdd r.free, laneCells r.outLanes outOdd 0, hb.in_eq, hb.out_eq,
        ⟨fun c ↦ ?_, fun c ↦ ?_⟩, rfl⟩
    · show (E.ofLimbs _ _ 0).limb 2 = 0
      rw [limb_ofLimbs]; rfl
    · rw [stateOfCells_laneCells, cellsOfState_eq_laneCells, ← hrel]

/-! ## The adapter to the prover data -/

/-- The table's `Spec`: the row refines `KeccakRefines` over the image the prover data names. -/
def KeccakSpec (r : KeccakRow K) (next : Regs K) (data : ProverData K) : Prop :=
  KeccakRefines (imageOf data).2 r next

/-! ## Proof helpers -/

/-- A cell limb in the layout a flag selects: the even lane at `0`, the odd one at `1`. -/
theorem layoutLimb_flag (a b : K) (odd : Bool) :
    a + flagK odd * a + flagK odd * b = if odd then b else a := by
  cases odd <;> simp [flagK, CharTwo.add_self_eq_zero]

/-- A cell limb holding the same lane in both layouts, and the others, in the layout a flag
selects (the forms `_layout_limb` takes with a missing lane). -/
theorem layoutLimb_flag' (a : K) (odd : Bool) :
    a + flagK odd * a = if odd then 0 else a := by
  cases odd <;> simp [flagK, CharTwo.add_self_eq_zero]

/-- The tuple of a `KECCAK` bytecode read, flat. -/
theorem keccak_tuple (c o0 o1 o2 o3 o4 o5 o6 o7 f1 f2 : K) :
    #v[c] ++ #v[o0, o1, o2, o3, o4, o5, o6, o7, f1, f2] =
      #v[c, o0, o1, o2, o3, o4, o5, o6, o7, f1, f2] := rfl

/-- The bytecode tuple of a row is `entry` of the instruction it names. -/
private theorem keccak_entry (om : Fin 4 → K) (otail ob8 ocap oout : K) (inOdd outOdd : Bool) :
    #v[Opcode.keccak.code] ++ #v[om 0, om 1, om 2, om 3, otail, ob8, ocap, oout, flagK inOdd,
      flagK outOdd] = entry (.keccak om otail ob8 ocap oout inOdd outOdd) := rfl

/-- The bytecode tuple of a row, its operands spelled out, is `entry` of the instruction it names. -/
private theorem keccak_entry' (a0 a1 a2 a3 otail ob8 ocap oout : K) (inOdd outOdd : Bool) :
    #v[Opcode.keccak.code] ++ #v[a0, a1, a2, a3, otail, ob8, ocap, oout, flagK inOdd,
      flagK outOdd] = entry (.keccak ![a0, a1, a2, a3] otail ob8 ocap oout inOdd outOdd) := rfl

/-- A decoding `KECCAK` tuple has `0/1` layout flags. -/
theorem keccak_flags_of_decode {c o0 o1 o2 o3 o4 o5 o6 o7 f1 f2 : K} {ins : Instr}
    (hc : c = Opcode.keccak.code)
    (h : decode #v[c, o0, o1, o2, o3, o4, o5, o6, o7, f1, f2] = some ins) :
    ∃ b1 b2, f1 = flagK b1 ∧ f2 = flagK b2 := by
  subst hc
  simp only [decode, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, opcode?_code] at h
  rcases h1 : flag? f1 with _ | b1 <;> rcases h2 : flag? f2 with _ | b2 <;>
    simp only [h1, h2, reduceCtorEq] at h
  exact ⟨b1, b2, flag?_eq_some_iff.mp h1, flag?_eq_some_iff.mp h2⟩

/-! ## The table -/

set_option maxHeartbeats 16000000 in
/-- The `KECCAK` table (`_flushes_keccak`, `verifier.py:888-916`): state step, bytecode read of
`(KECCAK, o_m₀, …, o_m₃, o_tail, o_b8, o_cap, o_out, odd_in, odd_out)`, the thirteen cells read
and the thirteen written, each as `(lo, hi, 0)` in its layout. Returns the pushed successor
`(g·pc, fp)`; sound under `KeccakRelation`. -/
def keccakTable : GeneralFormalCircuit K KeccakRow Regs where
  main r := do
    let next : Var Regs K := ⟨Expression.const g * r.pc, r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.keccak.code)
      #v[r.om[0], r.om[1], r.om[2], r.om[3], r.otail, r.ob8, r.ocap, r.oout, r.oddIn, r.oddOut]
    memRead (r.fp * r.om[0]) r.cnt[0] #v[r.lin[0] + r.oddIn * r.lin[0] + r.oddIn * r.free, r.lin[1] + r.oddIn * r.lin[1] + r.oddIn * r.lin[0], 0]
    memRead (r.fp * r.om[1]) r.cnt[1] #v[r.lin[2] + r.oddIn * r.lin[2] + r.oddIn * r.lin[1], r.lin[3] + r.oddIn * r.lin[3] + r.oddIn * r.lin[2], 0]
    memRead (r.fp * r.om[2]) r.cnt[2] #v[r.lin[4] + r.oddIn * r.lin[4] + r.oddIn * r.lin[3], r.lin[5] + r.oddIn * r.lin[5] + r.oddIn * r.lin[4], 0]
    memRead (r.fp * r.om[3]) r.cnt[3] #v[r.lin[6] + r.oddIn * r.lin[6] + r.oddIn * r.lin[5], r.lin[7] + r.oddIn * r.lin[7] + r.oddIn * r.lin[6], 0]
    memRead (r.fp * (Expression.const (g ^ 0) * r.otail)) r.cnt[4] #v[r.lin[8] + r.oddIn * r.lin[8] + r.oddIn * r.lin[7], r.lin[9] + r.oddIn * r.lin[9] + r.oddIn * r.lin[8], 0]
    memRead (r.fp * (Expression.const (g ^ 1) * r.otail)) r.cnt[5] #v[r.lin[10] + r.oddIn * r.lin[10] + r.oddIn * r.lin[9], r.lin[11] + r.oddIn * r.lin[11] + r.oddIn * r.lin[10], 0]
    memRead (r.fp * (Expression.const (g ^ 2) * r.otail)) r.cnt[6] #v[r.lin[12] + r.oddIn * r.lin[12] + r.oddIn * r.lin[11], r.lin[13] + r.oddIn * r.lin[13] + r.oddIn * r.lin[12], 0]
    memRead (r.fp * (Expression.const (g ^ 3) * r.otail)) r.cnt[7] #v[r.lin[14] + r.oddIn * r.lin[14] + r.oddIn * r.lin[13], r.lin[15] + r.oddIn * r.lin[15] + r.oddIn * r.lin[14], 0]
    memRead (r.fp * r.ob8) r.cnt[8] #v[r.lin[16] + r.oddIn * r.lin[16] + r.oddIn * r.lin[15], r.free + r.oddIn * r.free + r.oddIn * r.lin[16], 0]
    memRead (r.fp * (Expression.const (g ^ 0) * r.ocap)) r.cnt[9] #v[r.lin[17], r.lin[18], 0]
    memRead (r.fp * (Expression.const (g ^ 1) * r.ocap)) r.cnt[10] #v[r.lin[19], r.lin[20], 0]
    memRead (r.fp * (Expression.const (g ^ 2) * r.ocap)) r.cnt[11] #v[r.lin[21], r.lin[22], 0]
    memRead (r.fp * (Expression.const (g ^ 3) * r.ocap)) r.cnt[12] #v[r.lin[23], r.lin[24], 0]
    memRead (r.fp * (Expression.const (g ^ 0) * r.oout)) r.cnt[13] #v[r.lout[0] + r.oddOut * r.lout[0], r.lout[1] + r.oddOut * r.lout[1] + r.oddOut * r.lout[0], 0]
    memRead (r.fp * (Expression.const (g ^ 1) * r.oout)) r.cnt[14] #v[r.lout[2] + r.oddOut * r.lout[2] + r.oddOut * r.lout[1], r.lout[3] + r.oddOut * r.lout[3] + r.oddOut * r.lout[2], 0]
    memRead (r.fp * (Expression.const (g ^ 2) * r.oout)) r.cnt[15] #v[r.lout[4] + r.oddOut * r.lout[4] + r.oddOut * r.lout[3], r.lout[5] + r.oddOut * r.lout[5] + r.oddOut * r.lout[4], 0]
    memRead (r.fp * (Expression.const (g ^ 3) * r.oout)) r.cnt[16] #v[r.lout[6] + r.oddOut * r.lout[6] + r.oddOut * r.lout[5], r.lout[7] + r.oddOut * r.lout[7] + r.oddOut * r.lout[6], 0]
    memRead (r.fp * (Expression.const (g ^ 4) * r.oout)) r.cnt[17] #v[r.lout[8] + r.oddOut * r.lout[8] + r.oddOut * r.lout[7], r.lout[9] + r.oddOut * r.lout[9] + r.oddOut * r.lout[8], 0]
    memRead (r.fp * (Expression.const (g ^ 5) * r.oout)) r.cnt[18] #v[r.lout[10] + r.oddOut * r.lout[10] + r.oddOut * r.lout[9], r.lout[11] + r.oddOut * r.lout[11] + r.oddOut * r.lout[10], 0]
    memRead (r.fp * (Expression.const (g ^ 6) * r.oout)) r.cnt[19] #v[r.lout[12] + r.oddOut * r.lout[12] + r.oddOut * r.lout[11], r.lout[13] + r.oddOut * r.lout[13] + r.oddOut * r.lout[12], 0]
    memRead (r.fp * (Expression.const (g ^ 7) * r.oout)) r.cnt[20] #v[r.lout[14] + r.oddOut * r.lout[14] + r.oddOut * r.lout[13], r.lout[15] + r.oddOut * r.lout[15] + r.oddOut * r.lout[14], 0]
    memRead (r.fp * (Expression.const (g ^ 8) * r.oout)) r.cnt[21] #v[r.lout[16] + r.oddOut * r.lout[16] + r.oddOut * r.lout[15], r.oddOut * r.lout[16], 0]
    memRead (r.fp * (Expression.const (g ^ 9) * r.oout)) r.cnt[22] #v[r.lout[17], r.lout[18], 0]
    memRead (r.fp * (Expression.const (g ^ 10) * r.oout)) r.cnt[23] #v[r.lout[19], r.lout[20], 0]
    memRead (r.fp * (Expression.const (g ^ 11) * r.oout)) r.cnt[24] #v[r.lout[21], r.lout[22], 0]
    memRead (r.fp * (Expression.const (g ^ 12) * r.oout)) r.cnt[25] #v[r.lout[23], r.lout[24], 0]
    pure next
  -- The push channels: their requirements are vacuous, the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The named assumption: the Keccak reduction's proof of the permutation on the row's lanes.
  Assumptions r _ := KeccakRelation r
  Spec := KeccakSpec
  -- The local premise: the flags are layouts and the twenty-six cells are bound.
  ProverAssumptions r data _ := ∃ inOdd outOdd : Bool, r.oddIn = flagK inOdd ∧
    r.oddOut = flagK outOdd ∧ KeccakBindings (imageOf data).2 r inOdd outOdd
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hdec⟩, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩ := h_holds
    obtain ⟨_, _, hom, _, _, _, _, hoi, hoo, _, hlin, hlout, _, _⟩ := h_input
    subst hom hlin hlout
    rw [keccak_tuple] at hdec
    obtain ⟨inOdd, outOdd, hfi, hfo⟩ := keccak_flags_of_decode rfl hdec
    simp only [hfi] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    simp only [hfo] at h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
    refine (keccak_refines_iff _ _ _).mpr ⟨⟨inOdd, outOdd, hfi, hfo, ⟨fun c ↦ ?_, fun c ↦ ?_⟩⟩,
      h_assumptions, rfl⟩
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
      · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h25 ⊢ <;> exact h25
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨inOdd, outOdd, hfi, hfo, hb⟩ := h_assumptions
    obtain ⟨_, _, hom, _, _, _, _, hoi, hoo, _, hlin, hlout, _, _⟩ := h_input
    subst hom hlin hlout hfi hfo
    refine ⟨⟨_, by rw [keccak_entry']; exact decode_entry _⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h := hb.in_eq 0
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, KeccakRow.oms, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 1
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, KeccakRow.oms, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 2
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, KeccakRow.oms, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 3
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, KeccakRow.oms, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 4
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, pow_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 5
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul, pow_one] at h ⊢ <;> exact h
    · have h := hb.in_eq 6
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 7
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 8
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 9
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, Vector.getElem_map, pow_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 10
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, Vector.getElem_map, pow_one] at h ⊢ <;> exact h
    · have h := hb.in_eq 11
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, Vector.getElem_map] at h ⊢ <;> exact h
    · have h := hb.in_eq 12
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInOffset, KeccakRow.inLanes, Vector.getElem_map] at h ⊢ <;> exact h
    · have h := hb.out_eq 0
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, pow_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.out_eq 1
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul, pow_one] at h ⊢ <;> exact h
    · have h := hb.out_eq 2
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.out_eq 3
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.out_eq 4
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.out_eq 5
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.out_eq 6
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.out_eq 7
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.out_eq 8
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, flagK, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.out_eq 9
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h ⊢ <;> exact h
    · have h := hb.out_eq 10
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h ⊢ <;> exact h
    · have h := hb.out_eq 11
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h ⊢ <;> exact h
    · have h := hb.out_eq 12
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h ⊢ <;> exact h

/-! ## Rows from executions -/

/-- The cells a `KECCAK` with these operands reads at `fp` over the image, the zero word where a
read fails. -/
noncomputable def keccakInputCells {κ : ℕ} (mem : MemImage κ) (fp : K) (om : Fin 4 → K)
    (otail ob8 ocap : K) (c : Fin 13) : E :=
  (mem.read (fp * keccakInOffset om otail ob8 ocap c)).getD 0

/-- The row of an execution of `KECCAK om o_tail o_b8 o_cap o_out inOdd outOdd` from `(pc, fp)`
over the image `mem`: the registers, the operands, the layout flags, the input lanes the cells
read hold and their free limb, the output lanes Keccak-f[1600] of them, and the counts as
parameters. Noncomputable: it reads the image. -/
noncomputable def keccakRowOf {κ : ℕ} (mem : MemImage κ) (pc fp : K) (om : Fin 4 → K)
    (otail ob8 ocap oout : K) (inOdd outOdd : Bool) (cnt : Vector K 26) (rbc : K) :
    KeccakRow K :=
  let input := keccakInputCells mem fp om otail ob8 ocap
  let S := stateOfCells input inOdd
  ⟨pc, fp, #v[om 0, om 1, om 2, om 3], otail, ob8, ocap, oout, flagK inOdd, flagK outOdd,
    freeLimb input inOdd, Vector.ofFn (stateLanes S), Vector.ofFn (stateLanes (keccakF S)), cnt,
    rbc⟩

/-- The operands of `keccakRowOf` are the instruction's. -/
theorem keccakRowOf_oms {κ : ℕ} (mem : MemImage κ) (pc fp : K) (om : Fin 4 → K)
    (otail ob8 ocap oout : K) (inOdd outOdd : Bool) (cnt : Vector K 26) (rbc : K) :
    (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd cnt rbc).oms = om := by
  funext i; fin_cases i <;> rfl

/-- A valid execution of `KECCAK` is represented by `keccakRowOf`, with any counts: its input
cells are canonical, so they are the cells of the lanes they hold, and its output cells are the
cells of Keccak-f[1600] of those lanes. -/
theorem keccakRowOf_refines {κ : ℕ} {mem : MemImage κ} {pc fp : K} {om : Fin 4 → K}
    {otail ob8 ocap oout : K} {inOdd outOdd : Bool} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.keccak om otail ob8 ocap oout inOdd outOdd) = some next)
    (cnt : Vector K 26) (rbc : K) :
    KeccakRefines mem (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd cnt rbc) next := by
  obtain ⟨input, output, hin, hout, hcells, -⟩ :=
    (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _).mp hexec
  have hinput : keccakInputCells mem fp om otail ob8 ocap = input := by
    funext c; simp [keccakInputCells, hin c]
  have hlanes : (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd cnt rbc).inLanes =
      stateLanes (stateOfCells input inOdd) := by
    funext l; simp [keccakRowOf, KeccakRow.inLanes, hinput]
  have hlout : (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd cnt rbc).outLanes =
      stateLanes (keccakF (stateOfCells input inOdd)) := by
    funext l; simp [keccakRowOf, KeccakRow.outLanes, hinput]
  have hfree : (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd cnt rbc).free =
      freeLimb input inOdd := by
    simp [keccakRowOf, hinput]
  refine ⟨inOdd, outOdd, rfl, rfl, ⟨fun c ↦ ?_, fun c ↦ ?_⟩, ?_⟩
  · rw [hlanes, hfree, laneCells_stateOfCells hcells.1, keccakRowOf_oms]
    exact hin c
  · rw [hlout, ← cellsOfState_eq_laneCells, ← hcells.2 c]
    exact hout c
  · rw [keccakRowOf_oms]; exact hexec

/-- Every valid `KECCAK` execution has a satisfying row, from the execution alone. -/
theorem keccak_exec_complete {data : ProverData K} {pc fp : K} {om : Fin 4 → K}
    {otail ob8 ocap oout : K} {inOdd outOdd : Bool} {next : Regs K}
    (hexec : execute (imageOf data).2 ⟨pc, fp⟩ (.keccak om otail ob8 ocap oout inOdd outOdd) =
      some next) (cnt : Vector K 26) (rbc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((keccakTable.main (const (keccakRowOf (imageOf data).2 pc fp om otail ob8 ocap oout inOdd
        outOdd cnt rbc))).operations 0) := by
  obtain ⟨i, o, hi, ho, hb, -⟩ := keccakRowOf_refines hexec cnt rbc
  exact (keccakTable.completeness 0 (rowEnv data) (const _)
    (by simp only [circuit_norm, keccakTable, memRead, bytecodeRead, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover ⟨i, o, hi, ho, hb⟩).1

end LeanVM.Arithmetization
