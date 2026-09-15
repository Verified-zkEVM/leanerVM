import LeanerVM.Arithmetization.Boundary

/-!
# Layer 7 tests: the boundary blocks

A plain file, like the module it tests: the fixtures decide `E` arithmetic in the kernel. One
prover data serves the three blocks: a four-word image (`κ = 2`) and a two-slot program
(`logSize = 1`), read through `imageOf`/`programOf` at literal indices as in the Layer 5 and 6
tests.

The three components are pinned to the Rust blocks (`layout.rs:352-395`) as data: each is a
push at count `1` and a pull at the finalize count, on its channel pair, with the pull's
multiplicity `-1` and its guarantee assumed; the verifier has no local witness (the
`verifier_length_zero` field of Layer 8's ensemble) and is complete for every public input.
`PublicIO` flattens to the four lanes then the sentinel counter, and `PublicIO.ofInput` fixes
the counter to the program's.

For the two seed blocks: the honest row of a word or a slot is bound (`MemSpec`, `BytecodeSpec`)
and the row `memRowOf`/`bytecodeRowOf` builds from the image or the program alone satisfies the
constraints `main` emits (`mem_word_complete`, `bytecode_entry_complete`), with any finalize
count, `0` included, since nothing checks the finalize counts (specification §6.2). Rejections
use actual rows and the blocks' own theorems: a changed limb, the address `0` (acceptance test
2) and an address past the image fail `MemSpec` and hence the constraints in every environment
over the data (read back through `soundness`); a changed opcode, a nonzero spare slot
(acceptance test 16, finding R24) and a counter past the program fail `BytecodeSpec` the same
way.
-/

namespace LeanerVMTests.Arithmetization.Boundary

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization

/-! ## The fixture: four words, two slots -/

/-- The image: four words, `κ = 2`. -/
def memWords : Array (Vector K 3) := #[#v[1, 2, 3], #v[4, 5, 6], #v[7, 8, 9], #v[0, 0, 0]]

/-- The program: an `XOR` and a `JUMP`, `logSize = 1`. -/
def progEntries : Array (Vector K 8) :=
  #[entry (.xor (gpow 2) (gpow 3) (gpow 4)), entry (.jump 1 1 1)]

/-- The prover data, its two tables told apart by arity so that the kernel never compares
names (as in the Layer 5 and 6 tests). -/
def bData : ProverData K := fun _ n ↦
  match n with
  | 3 => memWords
  | 8 => progEntries
  | _ => #[]

theorem bData_logSize : (imageOf bData).1 = 2 := by
  show min (Nat.log 2 (memRows bData).size) maxLogMem = 2
  rw [show (memRows bData).size = 4 from rfl, show (4 : ℕ) = 2 ^ 2 by decide,
    Nat.log_pow (by norm_num)]
  decide

theorem bData_progLogSize : (programOf bData).logSize = 1 := by
  show min (Nat.log 2 (bytecodeRows bData).size) maxLogBytecode = 1
  have h := Nat.log_pow (b := 2) (by norm_num) 1
  rw [pow_one] at h
  rw [show (bytecodeRows bData).size = 2 from rfl, h]
  decide

theorem bData_wellShaped : WellShapedData bData where
  memRows_size := by rw [bData_logSize]; rfl
  bytecodeRows_size := by rw [bData_progLogSize]; rfl

/-- The word at `g^k` of the fixture's image, as limbs. -/
theorem read_at (k : ℕ) (v : Vector K 3) (hk : k < 4 := by decide)
    (hv : memWords[k]'(by rw [show memWords.size = 4 from rfl]; exact hk) = v :=
      by decide +kernel) :
    (imageOf bData).2.read (gpow k) = some (E.ofLimbs v[0] v[1] v[2]) := by
  have hk' : k < 2 ^ (imageOf bData).1 := by rw [bData_logSize]; omega
  rw [show gpow k = gpow ((⟨k, hk'⟩ : Fin (2 ^ (imageOf bData).1)) : ℕ) from rfl,
    MemImage.read_gpow (by rw [bData_logSize]; decide), imageOf_apply bData_wellShaped _ hv]

/-- The instruction at `g^i` of the fixture's program, decoded. -/
theorem fetch_at (i : ℕ) (ins : Instr) (hi : i < 2 := by decide)
    (hd : decode (progEntries[i]'(by rw [show progEntries.size = 2 from rfl]; exact hi)) =
      some ins := by decide +kernel) :
    (programOf bData).fetch (gpow i) = some ins := by
  have hi' : i < 2 ^ (programOf bData).logSize := by rw [bData_progLogSize]; omega
  rw [show gpow i = gpow ((⟨i, hi'⟩ : Fin (2 ^ (programOf bData).logSize)) : ℕ) from rfl,
    Program.fetch_gpow, programOf_code bData_wellShaped ⟨i, hi'⟩ hd]

/-! ## The three blocks are their flushes (`layout.rs:352-395`) -/

/-- The memory block: the seed push at count `1`, the finalize pull at `cntFin`, on the memory
pair. -/
example (r : Var MemRow K) : (memTable.main r).operations 0 =
    [.interact ⟨MemPush.toRaw, 1, toElements (⟨r.idx, 1, r.m⟩ : MemMsg (Expression K)), false⟩,
     .interact ⟨MemPull.toRaw, -1, toElements (⟨r.idx, r.cntFin, r.m⟩ : MemMsg (Expression K)),
       true⟩] :=
  rfl

/-- The bytecode block, likewise, on the bytecode pair. -/
example (r : Var BytecodeRow K) : (bytecodeTable.main r).operations 0 =
    [.interact ⟨BytecodePush.toRaw, 1,
       toElements (⟨r.idx, 1, r.opcode, r.op⟩ : BytecodeMsg (Expression K)), false⟩,
     .interact ⟨BytecodePull.toRaw, -1,
       toElements (⟨r.idx, r.cntFin, r.opcode, r.op⟩ : BytecodeMsg (Expression K)), true⟩] :=
  rfl

/-- The verifier: push `(1, 1)`, pull `(finalPc, 1)`, on the state pair (specification §6.1). -/
example (pi : Var PublicIO K) : (leanIsaVerifier.main pi).operations 0 =
    [.interact ⟨StatePush.toRaw, 1, toElements (⟨1, 1⟩ : Regs (Expression K)), false⟩,
     .interact ⟨StatePull.toRaw, -1, toElements (⟨pi.finalPc, 1⟩ : Regs (Expression K)),
       true⟩] :=
  rfl

/-- The seed count is the word `1 = g^0`. -/
example (env : Environment K) : Expression.eval env (1 : Expression K) = gpow 0 := by
  simp only [circuit_norm]; rfl

/-- The verifier has no local witness: the `verifier_length_zero` field of Layer 8's ensemble. -/
example (pi : Var PublicIO K) : leanIsaVerifier.localLength pi = 0 := by
  simp only [circuit_norm, leanIsaVerifier]

/-- The verifier is complete for every public input over every data. -/
example (pi : PublicIO K) (data : ProverData K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((leanIsaVerifier.main (const pi)).operations 0) :=
  (leanIsaVerifier.completeness 0 (rowEnv data) (const pi)
    (by simp only [circuit_norm, leanIsaVerifier, -BitVec.reduceNeg]) pi
    ProvableType.eval_const_prover trivial).1

/-! ## The public input -/

-- The four lanes, then the sentinel counter.
#guard (toElements (⟨#v[1, 2, 3, 4], 5⟩ : PublicIO K)).toList = [1, 2, 3, 4, 5]
#guard (toElements (PublicIO.ofInput (programOf bData) ⟨![7, 8, 9, 10]⟩)).toList =
  [7, 8, 9, 10, gpow 1]

-- Five coordinates.
example : size PublicIO = 5 := rfl

/-- `PublicIO.ofInput` fixes the counter to the program's sentinel `g^(N_prog - 1)`: `g^1` for
the two-slot program. -/
example (input : PublicInput) :
    (PublicIO.ofInput (programOf bData) input).finalPc = (programOf bData).finalPc := rfl

example (input : PublicInput) : (PublicIO.ofInput (programOf bData) input).finalPc = gpow 1 := by
  show gpow (2 ^ (programOf bData).logSize - 1) = gpow 1
  rw [bData_progLogSize]
  rfl

/-! ## The memory block -/

/-- The honest seed row of word `1`: `(g^1, g^3, (4, 5, 6))`, read three times. -/
def memRow1 : MemRow K := ⟨gpow 1, gpow 3, #v[4, 5, 6]⟩

/-- The honest row is bound to the image. -/
theorem memRow1_spec : MemSpec memRow1 bData := ⟨read_at 1 #v[4, 5, 6]⟩

/-- Nothing checks the finalize count (specification §6.2): the same row with count `0` is
bound too. -/
example : MemSpec { memRow1 with cntFin := 0 } bData := ⟨read_at 1 #v[4, 5, 6]⟩

/-- The row `memRowOf` builds from the image is the honest row. -/
example : memRowOf (imageOf bData).2 ⟨1, by rw [bData_logSize]; decide⟩ (gpow 3) = memRow1 := by
  rw [memRowOf, imageOf_apply bData_wellShaped _ (v := #v[4, 5, 6]) (by decide +kernel)]
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
def memRow1' : MemRow K := { memRow1 with m := #v[4, 5, 7] }

theorem memRow1'_not_spec : ¬ MemSpec memRow1' bData := by
  rintro ⟨h⟩
  rw [show memRow1'.idx = gpow 1 from rfl, read_at 1 #v[4, 5, 6]] at h
  exact absurd (Option.some.inj h) (by decide +kernel)

/-- … and the constraints `main` emits on it fail in every environment over the data: its pull
is no read of the image (`soundness`, read back). -/
example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, bData⟩ ((memTable.main (const memRow1')).operations 0) :=
  fun h ↦ memRow1'_not_spec
    (memTable.soundness 0 ⟨get, bData⟩ (const memRow1') memRow1' ProvableType.eval_const
      trivial h).1

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

/-- The honest row is bound to the program: its entry is the fetched instruction's. -/
theorem bcRow0_spec : BytecodeSpec bcRow0 bData :=
  ⟨_, fetch_at 0 (.xor (gpow 2) (gpow 3) (gpow 4)), by decide +kernel⟩

/-- The row `bytecodeRowOf` builds from the program is the honest row, and slot `1` gives the
`JUMP` entry with its four spare slots zero. -/
theorem slot0_lt : 0 < 2 ^ (programOf bData).logSize := by rw [bData_progLogSize]; decide
theorem slot1_lt : 1 < 2 ^ (programOf bData).logSize := by rw [bData_progLogSize]; decide

example : bytecodeRowOf (programOf bData) ⟨0, slot0_lt⟩ (gpow 2) = bcRow0 := by
  have h : (programOf bData).code ⟨0, slot0_lt⟩ = .xor (gpow 2) (gpow 3) (gpow 4) :=
    programOf_code bData_wellShaped _ (by decide +kernel)
  simp only [bytecodeRowOf, h]
  rfl

example : bytecodeRowOf (programOf bData) ⟨1, slot1_lt⟩ 1 =
    ⟨gpow 1, 1, Opcode.jump.code, #v[1, 1, 1, 0, 0, 0, 0]⟩ := by
  have h : (programOf bData).code ⟨1, slot1_lt⟩ = .jump 1 1 1 :=
    programOf_code bData_wellShaped _ (by decide +kernel)
  simp only [bytecodeRowOf, h]
  rfl

/-- Every slot of the program has a satisfying seed row from the program alone
(`bytecode_entry_complete`), with any count. -/
example : ConstraintsHold.Completeness (rowEnv bData)
    ((bytecodeTable.main (const (bytecodeRowOf (programOf bData) ⟨0, slot0_lt⟩
      (gpow 2)))).operations 0) :=
  bytecode_entry_complete _ _

example : ConstraintsHold.Completeness (rowEnv bData)
    ((bytecodeTable.main (const (bytecodeRowOf (programOf bData) ⟨1, slot1_lt⟩
      0))).operations 0) :=
  bytecode_entry_complete _ _

/-- A changed opcode: the row's entry is not the fetched instruction's, so it is not bound … -/
def bcRow0' : BytecodeRow K := { bcRow0 with opcode := Opcode.mulNative.code }

theorem bcRow0'_not_spec : ¬ BytecodeSpec bcRow0' bData := by
  rintro ⟨ins, hfetch, hdec⟩
  rw [show bcRow0'.idx = gpow 0 from rfl, fetch_at 0 (.xor (gpow 2) (gpow 3) (gpow 4))] at hfetch
  obtain rfl := Option.some.inj hfetch
  exact absurd hdec (by decide +kernel)

/-- … and the constraints fail in every environment over the data (`soundness`, read back). -/
example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, bData⟩
      ((bytecodeTable.main (const bcRow0')).operations 0) :=
  fun h ↦ bcRow0'_not_spec
    (bytecodeTable.soundness 0 ⟨get, bData⟩ (const bcRow0') bcRow0' ProvableType.eval_const
      trivial h).1

/-- A nonzero spare slot is no instruction (acceptance test 16, finding R24): the row decodes to
nothing and is bound to nothing, whatever the program fetches. -/
def bcRow0'' : BytecodeRow K := { bcRow0 with op := #v[gpow 2, gpow 3, gpow 4, 0, 0, 0, 1] }

example : ¬ BytecodeSpec bcRow0'' bData := by
  rintro ⟨ins, -, hdec⟩
  rw [show decode (#v[bcRow0''.opcode] ++ bcRow0''.op) = none by decide +kernel] at hdec
  cases hdec

/-- A counter past the program, `g^2` at `logSize = 1`, fetches nothing. -/
example (cntFin opcode : K) (op : Vector K 7) :
    ¬ BytecodeSpec ⟨gpow 2, cntFin, opcode, op⟩ bData := by
  rintro ⟨ins, hfetch, -⟩
  rw [Program.fetch, gLog?_gpow_eq_none (by rw [bData_progLogSize]; decide) (by decide),
    Option.map_none] at hfetch
  cases hfetch

end LeanerVMTests.Arithmetization.Boundary
