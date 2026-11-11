import LeanerVM.Arithmetization.Boundary

/-!
# Layer 7 tests: the boundary blocks

A classic test for kernel evaluation: the fixtures decide `E` arithmetic in the kernel. One
prover data serves the three blocks, the four rows of a memory block of log-size `κ = 2` under
its name (`"mem"`, the image `imageOf` reads), read at literal indices as in the Layer 5 and 6
tests, beside a two-slot program `bProg` (`logSize = 1`), a `Program` value: the program is
public and no table of the data (decision 14).

The three blocks are pinned to the Rust blocks (`layout.rs:352-395`) as data: each is a push at
count `1` and a pull at the finalize count on its one channel, told apart by their direction
tags; the verifier of a program pushes the initial state and pulls the program's sentinel as a
constant, `g^1` for the fixture's two-slot program. `PublicIO` flattens to the four lanes.

**Fixed columns.** The index column `gpowCell` is `g^i` at rows `0` to `3` of a block of
log-size `2`. A memory row agrees with the memory block's fixed cells at row `i` exactly when its
address is `g^i` (`memMode_fixedAt_iff`), and a bytecode row agrees with the bytecode block's at
row `i` exactly when it is the program's slot `i` (`bytecodeMode_fixedAt_iff`): a shifted
address, a changed opcode and a nonzero spare slot are rejected by the components, since a fixed
column cannot be overwritten (issue #23), and a bytecode block of the wrong height has no
`FixedRowsMatch`.

**The specifications.** The honest row of a word is row `i` of the data's table at `g^i`
(`MemSeed`, the block's `Assumptions`) and is bound (`MemSpec`); the honest row of a slot
decodes (`BytecodeDecodes`, the block's `Assumptions` and `Spec`) and is the program's
(`BytecodeBindings bProg`), and the row `memRowOf`/`bytecodeRowOf` builds from the image or the
program alone is the honest row and satisfies the constraints `main` emits
(`mem_word_complete`, `bytecode_entry_complete`), with any finalize count, `0` included, since
nothing checks the finalize counts (specification §6.2). Rejections use actual rows: a changed
limb fails `MemSeed` and `MemSpec`, the address `0` (acceptance test 2) and an address past the
image fail `MemSpec`; a nonzero spare slot (acceptance test 16, finding R24) fails
`BytecodeDecodes`; a changed opcode decodes, so the circuit accepts it, and is rejected by the
fixed entry columns and by `BytecodeBindings bProg` (decision 14).
-/
namespace LeanerVMTests.Arithmetization.Boundary

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization

/-! ## The fixture: four words, two slots -/

/-- The program: an `XOR` and a `JUMP`, `logSize = 1`, a `Program` value (public, not data). -/
def bProg : Program := ⟨1, by decide, ![.xor (gpow 2) (gpow 3) (gpow 4), .jump 1 1 1]⟩

/-- The prover data: the memory block's four rows `(g^i, 1, mem[i])`, matched on arity so that
the kernel never compares names (as in the Layer 5 and 6 tests). -/
def bData : ProverData K := fun _ n ↦
  match n with
  | 5 => #[#v[gpow 0, 1, 1, K.ofBits 2, K.ofBits 3],
      #v[gpow 1, 1, K.ofBits 4, K.ofBits 5, K.ofBits 6],
      #v[gpow 2, 1, K.ofBits 7, K.ofBits 8, K.ofBits 9], #v[gpow 3, 1, 0, 0, 0]]
  | _ => #[]

theorem bData_logSize : (imageOf bData).1 = 2 := imageOf_fst (by decide) (by decide +kernel)

/-- The word at `g^k` of the fixture's image, as limbs. -/
theorem read_at (k : ℕ) (v : Vector K 3) (hk : k < 4 := by decide)
    (hv : (memRows bData)[k]? = some v := by decide +kernel) :
    (imageOf bData).2.read (gpow k) = some (E.ofLimbs v[0] v[1] v[2]) := by
  have hk' : k < 2 ^ (imageOf bData).1 := by rw [bData_logSize]; omega
  rw [show gpow k = gpow ((⟨k, hk'⟩ : Fin (2 ^ (imageOf bData).1)) : ℕ) from rfl,
    MemImage.read_gpow (by rw [bData_logSize]; decide), imageOf_apply _ hv]

/-- The instruction at `g^i` of the fixture's program. -/
theorem fetch_at (i : ℕ) (ins : Instr) (hi : i < 2 ^ bProg.logSize := by decide)
    (hd : bProg.code ⟨i, hi⟩ = ins := by rfl) : bProg.fetch (gpow i) = some ins := by
  rw [show gpow i = gpow ((⟨i, hi⟩ : Fin (2 ^ bProg.logSize)) : ℕ) from rfl,
    Program.fetch_gpow, hd]

/-! ## The three blocks are their flushes (`layout.rs:352-395`) -/

/-- The memory block: the seed push at count `1`, the finalize pull at `cntFin`, on the memory
channel. -/
example (r : Var MemRow K) : (memTable.main r).operations 0 =
    [.interact ⟨MemChannel.toRaw, .push, 1,
       toElements (⟨r.idx, 1, r.m⟩ : MemMsg (Expression K))⟩,
     .interact ⟨MemChannel.toRaw, .pull, 1,
       toElements (⟨r.idx, r.cntFin, r.m⟩ : MemMsg (Expression K))⟩] :=
  rfl

/-- The bytecode block, likewise, on the bytecode channel. -/
example (r : Var BytecodeRow K) : (bytecodeTable.main r).operations 0 =
    [.interact ⟨BytecodeChannel.toRaw, .push, 1,
       toElements (⟨r.idx, 1, r.opcode, r.op⟩ : BytecodeMsg (Expression K))⟩,
     .interact ⟨BytecodeChannel.toRaw, .pull, 1,
       toElements (⟨r.idx, r.cntFin, r.opcode, r.op⟩ : BytecodeMsg (Expression K))⟩] :=
  rfl

/-- The verifier of `prog`: push `(1, 1)`, pull `(prog.finalPc, 1)`, both constants, on the state
channel (specification §6.1; `layout.rs:354-358`). -/
example (prog : Program) : (leanIsaVerifier prog).interactions =
    [⟨StateChannel.toRaw, .push, 1, toElements (⟨1, 1⟩ : Regs (Expression K))⟩,
     ⟨StateChannel.toRaw, .pull, 1,
       toElements (⟨Expression.const prog.finalPc, 1⟩ : Regs (Expression K))⟩] :=
  rfl

/-- Its pull is granted the state channel's guarantee and its push owes it, on one channel. -/
example (prog : Program) :
    (leanIsaVerifier prog).channels = [StateChannel.toRaw, StateChannel.toRaw] :=
  rfl

/-- The seed count is the word `1 = g^0`. -/
example (env : Environment K) : Expression.eval env (1 : Expression K) = gpow 0 := by
  simp only [circuit_norm]; rfl

/-- The two boundary states are Layer 3's: `(1, 1)`, and `(g^(N_prog - 1), 1)`, which is
`(g^1, 1)` for the fixture's two-slot program. -/
example (env : Environment K) : eval env (⟨1, 1⟩ : Regs (Expression K)) = Regs.initial :=
  verifier_push_eval env

example (env : Environment K) :
    eval env (⟨Expression.const bProg.finalPc, 1⟩ : Regs (Expression K)) = ⟨gpow 1, 1⟩ := by
  rw [verifier_pull_eval]
  rfl

/-! ## The public input -/

-- The four lanes, and nothing else: the sentinel counter is the verifier's constant.
#guard (toElements (⟨#v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4]⟩ : PublicIO K)).toList = [1, K.ofBits 2, K.ofBits 3, K.ofBits 4]
#guard (toElements (PublicIO.ofInput ⟨![K.ofBits 7, K.ofBits 8, K.ofBits 9, K.ofBits 10]⟩)).toList = [K.ofBits 7, K.ofBits 8, K.ofBits 9, K.ofBits 10]

-- Four coordinates.
example : size PublicIO = 4 := rfl

/-! ## The index column -/

/-- The index column is `g^i` at the four rows of a block of log-size `2`. -/
example (env : ProverEnvironment K) (locals : Array (K ⊕ UInt64)) :
    (gpowCell .idx 2).eval ⟨env, locals, 0⟩ = gpow 0 ∧
      (gpowCell .idx 2).eval ⟨env, locals, 1⟩ = gpow 1 ∧
      (gpowCell .idx 2).eval ⟨env, locals, 2⟩ = gpow 2 ∧
        (gpowCell .idx 2).eval ⟨env, locals, 3⟩ = gpow 3 :=
  ⟨gpowCell_idx_eval (by decide) (by decide) _ _, gpowCell_idx_eval (by decide) (by decide) _ _,
    gpowCell_idx_eval (by decide) (by decide) _ _, gpowCell_idx_eval (by decide) (by decide) _ _⟩

/-- Over no bits it is the constant `1`. -/
example (ctx : Witgen.Ctx K) : (gpowCell .idx 0).eval ctx = 1 := rfl

/-! ## The memory block -/

/-- The honest seed row of word `1`: `(g^1, g^3, (4, 5, 6))`, read three times. -/
def memRow1 : MemRow K := ⟨gpow 1, gpow 3, #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]⟩

/-- The honest row is bound to the image. -/
theorem memRow1_spec : MemSpec memRow1 bData := ⟨read_at 1 #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]⟩

/-- Nothing checks the finalize count (specification §6.2): the same row with count `0` is
bound too. -/
example : MemSpec { memRow1 with cntFin := 0 } bData := ⟨read_at 1 #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]⟩

/-- It is row `1` of the data's table at `g^1`: the block's `Assumptions`, which the component
supplies from its fixed address column and the derived data. -/
theorem memRow1_seed : MemSeed memRow1 bData :=
  ⟨⟨⟨1, by rw [bData_logSize]; decide⟩, rfl, by decide +kernel⟩⟩

/-- Its address agrees with the fixed address column at row `1` … -/
example : (memMode 2).FixedAt (UInt64.ofNat 1) memRow1 :=
  (memMode_fixedAt_iff (by decide) (by decide) _).mpr rfl

/-- … and a shifted address does not: the index column cannot be overwritten (§6.5). -/
example : ¬ (memMode 2).FixedAt (UInt64.ofNat 1) { memRow1 with idx := gpow 2 } := fun h ↦ by
  have h' := (memMode_fixedAt_iff (by decide) (by decide) _).mp h
  revert h'
  decide +kernel

/-- The row `memRowOf` builds from the image is the honest row. -/
example : memRowOf (imageOf bData).2 ⟨1, by rw [bData_logSize]; decide⟩ (gpow 3) = memRow1 := by
  rw [memRowOf, imageOf_apply _ (v := #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]) (by decide +kernel)]
  simp only [limb_ofLimbs]
  rfl

/-- Every word of the image has a satisfying seed row from the image alone
(`mem_word_complete`), with any count: word `1` at `g^3`, word `3` at `0`. -/
example : ConstraintsHold.Completeness (rowEnv bData)
    ((memTable.main (const (memRowOf (imageOf bData).2 ⟨1, by rw [bData_logSize]; decide⟩
      (gpow 3)))).operations 0) :=
  mem_word_complete _ _

example : ConstraintsHold.Completeness (rowEnv bData)
    ((memTable.main (const (memRowOf (imageOf bData).2 ⟨3, by rw [bData_logSize]; decide⟩
      0))).operations 0) :=
  mem_word_complete _ _

/-- A changed limb: the row is no word of the image, so it is not bound … -/
def memRow1' : MemRow K := { memRow1 with m := #v[K.ofBits 4, K.ofBits 5, K.ofBits 7] }

theorem memRow1'_not_spec : ¬ MemSpec memRow1' bData := by
  rintro ⟨h⟩
  rw [show memRow1'.idx = gpow 1 from rfl, read_at 1 #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]] at h
  exact absurd (Option.some.inj h) (by decide +kernel)

/-- … nor row `1` of the data's table: the block's `Assumptions` reject it, so no witness has it
in its memory block. -/
example : ¬ MemSeed memRow1' bData := fun h ↦ memRow1'_not_spec h.spec

/-- The honest row's `Spec` follows from its `Assumptions` and the constraints, in every
environment over the data (`soundness`). -/
example (get : ℕ → K)
    (h : ConstraintsHold.Soundness ⟨get, bData⟩ ((memTable.main (const memRow1)).operations 0)) :
    MemSpec memRow1 bData :=
  (memTable.soundness 0 ⟨get, bData⟩ (const memRow1) memRow1 ProvableType.eval_const
    memRow1_seed h).1

/-- The address `0` is no address (acceptance test 2): a row there is bound to nothing. -/
example (cntFin : K) (m : Vector K 3) : ¬ MemSpec ⟨0, cntFin, m⟩ bData := by
  rintro ⟨h⟩
  rw [MemImage.read_zero] at h
  cases h

/-- An address past the image, `g^4` at `κ = 2`, is no address either. -/
example (cntFin : K) (m : Vector K 3) : ¬ MemSpec ⟨gpow 4, cntFin, m⟩ bData := by
  rintro ⟨h⟩
  rw [MemImage.read, gLog?_gpow_eq_none (by rw [bData_logSize]; decide) (by decide),
    Option.map_none] at h
  cases h

/-! ## The bytecode block -/

/-- The honest seed row of slot `0`: the `XOR` entry, executed twice. -/
def bcRow0 : BytecodeRow K :=
  ⟨gpow 0, gpow 2, Opcode.xor.code, #v[gpow 2, gpow 3, gpow 4, 0, 0, 0, 0]⟩

/-- The honest row decodes: the block's `Spec`, over no data. -/
theorem bcRow0_decodes : BytecodeDecodes bcRow0 :=
  ⟨.xor (gpow 2) (gpow 3) (gpow 4), by decide +kernel⟩

/-- … and is the program's: its entry is the instruction fetched at its counter, the per-row
reading of Layer 8's conjunct, which the block does not state. -/
theorem bcRow0_bindings : BytecodeBindings bProg bcRow0 :=
  ⟨_, fetch_at 0 (.xor (gpow 2) (gpow 3) (gpow 4)), by decide +kernel⟩

/-- The two slot indices of the fixture's program. -/
theorem slot0_lt : 0 < 2 ^ bProg.logSize := by decide
theorem slot1_lt : 1 < 2 ^ bProg.logSize := by decide

/-- The honest row agrees with the block's fixed columns at row `0`: its counter is `g^0` and its
entry the program's. -/
theorem bcRow0_fixed : (bytecodeMode bProg).FixedAt (UInt64.ofNat 0) bcRow0 :=
  (bytecodeMode_fixedAt_iff bProg slot0_lt _).mpr ⟨rfl, by decide +kernel⟩

/-- The row `bytecodeRowOf` builds from the program is the honest row, and slot `1` gives the
`JUMP` entry with its four spare slots zero: the block's rows are a function of the program,
the finalize count aside. -/
example : bytecodeRowOf bProg ⟨0, slot0_lt⟩ (gpow 2) = bcRow0 := rfl

example : bytecodeRowOf bProg ⟨1, slot1_lt⟩ 1 =
    ⟨gpow 1, 1, Opcode.jump.code, #v[1, 1, 1, 0, 0, 0, 0]⟩ :=
  rfl

/-- Every slot of the program has a satisfying seed row from the program alone
(`bytecode_entry_complete`), with any count, over any data. -/
example : ConstraintsHold.Completeness (rowEnv bData)
    ((bytecodeTable.main (const (bytecodeRowOf bProg ⟨0, slot0_lt⟩ (gpow 2)))).operations 0) :=
  bytecode_entry_complete bProg _ _

example (data : ProverData K) : ConstraintsHold.Completeness (rowEnv data)
    ((bytecodeTable.main (const (bytecodeRowOf bProg ⟨1, slot1_lt⟩ 0))).operations 0) :=
  bytecode_entry_complete bProg _ _

/-- A changed opcode: the row still decodes, so the block accepts it, its `Spec` naming no
program (leanVM's block carries the program as public columns it does not check) … -/
def bcRow0' : BytecodeRow K := { bcRow0 with opcode := Opcode.mulNative.code }

example : BytecodeDecodes bcRow0' :=
  ⟨.mulNative (gpow 2) (gpow 3) (gpow 4), by decide +kernel⟩

/-- … but the component rejects it: its entry columns are fixed to the program's, and a fixed
column cannot be overwritten (issue #23) … -/
example : ¬ (bytecodeMode bProg).FixedAt (UInt64.ofNat 0) bcRow0' := fun h ↦ by
  have h' := ((bytecodeMode_fixedAt_iff bProg slot0_lt _).mp h).2
  revert h'
  decide +kernel

/-- … and it is not the program's: `BytecodeBindings bProg` rejects it. -/
theorem bcRow0'_not_bound : ¬ BytecodeBindings bProg bcRow0' := by
  rintro ⟨ins, hfetch, hdec⟩
  rw [show bcRow0'.idx = gpow 0 from rfl, fetch_at 0 (.xor (gpow 2) (gpow 3) (gpow 4))] at hfetch
  obtain rfl := Option.some.inj hfetch
  exact absurd hdec (by decide +kernel)

/-- A nonzero spare slot is no instruction (acceptance test 16, finding R24): the row decodes to
nothing, fails the block's `Spec` … -/
def bcRow0'' : BytecodeRow K := { bcRow0 with op := #v[gpow 2, gpow 3, gpow 4, 0, 0, 0, 1] }

theorem bcRow0''_not_decodes : ¬ BytecodeDecodes bcRow0'' := by
  rintro ⟨ins, hdec⟩
  rw [show decode (#v[bcRow0''.opcode] ++ bcRow0''.op) = none by decide +kernel] at hdec
  cases hdec

/-- … fails the block's `Assumptions`, over any data, and the fixed entry columns. -/
example (data : ProverData K) : ¬ bytecodeTable.Assumptions bcRow0'' data :=
  bcRow0''_not_decodes

example : ¬ (bytecodeMode bProg).FixedAt (UInt64.ofNat 0) bcRow0'' := fun h ↦ by
  have h' := ((bytecodeMode_fixedAt_iff bProg slot0_lt _).mp h).2
  revert h'
  decide +kernel

/-- A counter past the program, `g^2` at `logSize = 1`, fetches nothing: the row is no slot of
the program, whatever its entry, though the block accepts a decodable one. -/
example (cntFin opcode : K) (op : Vector K 7) :
    ¬ BytecodeBindings bProg ⟨gpow 2, cntFin, opcode, op⟩ := by
  rintro ⟨ins, hfetch, -⟩
  rw [Program.fetch, gLog?_gpow_eq_none (by decide) (by decide), Option.map_none] at hfetch
  cases hfetch

/-- The bytecode block has the program's height: three rows are no block of `bProg`. -/
example : ¬ (bytecodeComponent bProg).FixedRowsMatch
    [(toElements bcRow0).toArray, (toElements bcRow0).toArray, (toElements bcRow0).toArray] :=
  fun h ↦ by
    obtain ⟨hl, -⟩ := h
    exact absurd hl (by decide)

end LeanerVMTests.Arithmetization.Boundary
