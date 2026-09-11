import LeanerVM.Arithmetization.Tables.Xor
import LeanerVM.Arithmetization.Tables.MulNative
import LeanerVM.Arithmetization.Tables.SetConstant
import LeanerVM.Arithmetization.Tables.Deref
import LeanerVM.Arithmetization.Tables.Jump
import LeanerVM.Arithmetization.Tables.Blake2s

/-!
# Layer 6 tests: the six opcode tables

A plain file, like the modules it tests: the fixtures decide `E` arithmetic and `Regs`
equalities in the kernel. One prover data serves every table: a thirty-two-word image
(`κ = 5`) and an eight-slot program with one instruction per opcode, both read through
`imageOf`/`programOf` at literal indices as in the Layer 5 tests.

For each table: the honest row satisfies `ProverAssumptions`, the hypothesis under which
`completeness` accepts it (for `XOR` the acceptance is exhibited literally, as
`ConstraintsHold.Completeness` on the row's environment; for `JUMP` the two honest witnesses
are checked against the residuals);
`Spec` holds of it, as the kernel-decided step of Layer 3; and one mutated row is rejected: a
wrong result limb (`XOR`, `MUL_NATIVE`), a wrong immediate limb (`SET_CONSTANT`), a flag pair
that is no store mode (`DEREF`), the flag row `b = 1, v_cond = 0` (`JUMP`, roadmap acceptance
test 8), and a non-canonical cell (`BLAKE2S`, acceptance test 12). A rejection is the failure
of the row's pull guarantee, which the bus cannot balance (Layer 9), or of a constraint.

The `MUL_NATIVE` row reproduces the executor's `mul_192bit_word` product (`cpu/mod.rs:981-998`,
`scripts/dump-mul-rust.sh`) from the twelve-product coordinates (acceptance test 9), and the
`BLAKE2S` row the cells of `blake2s_computes_the_compression` (`scripts/dump-blake2s-rust.sh`).
-/

namespace LeanerVMTests.Arithmetization.Tables

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization

/-! ## The fixture: one image, one program -/

-- scripts/dump-mul-rust.sh at leanVM a386121f: the operands `x`, `y` and the product `x · y`.
def x0 : K := 0x0123456789abcdef
def x1 : K := 0xfeedfacedeadbeef
def x2 : K := 0x1111222233334444
def y0 : K := 0x9999aaaabbbbcccc
def y1 : K := 0x13579bdf2468ace0
def y2 : K := 0x5555666677778888
def mulXY : E := E.ofLimbs 0xf4bccd9a2e8e525b 0xf85ebb9433986f2f 0x918137982bf175ac

-- scripts/dump-blake2s-rust.sh at leanVM a386121f: the nine cells, as `(lo, hi)`.
def rustM0 : Vector K 2 := #v[0x0123456789abcdef, 0xfedcba9876543210]
def rustM1 : Vector K 2 := #v[0x1111222233334444, 0x5555666677778888]
def rustM2 : Vector K 2 := #v[0xdeadbeefcafebabe, 0x0badf00d0badf00d]
def rustM3 : Vector K 2 := #v[0x9999aaaabbbbcccc, 0xddddeeeeffff0000]
def rustCv0 : Vector K 2 := #v[0x0000000000000007, 0x0000000000000000]
def rustCv1 : Vector K 2 := #v[0x000000000000000b, 0x0000000000000000]
def rustMd : Vector K 2 := #v[0x0000000000000040, 0x00000000ffffffff]
def rustOut0 : Vector K 2 := #v[0x583fffe1350e2137, 0x0de9e32629a5c508]
def rustOut1 : Vector K 2 := #v[0xf1b0679a15df60bb, 0x0228c8d4ed9b3a24]

/-- The canonical image word of a two-limb cell. -/
def cell (v : Vector K 2) : Vector K 3 := #v[v[0], v[1], 0]

/-- The twelve-product coordinates of `x · y` (`TOWER_LANES`). -/
def xyLanes : Vector K 3 :=
  #v[x0 * y0 + x1 * y2 + x2 * y1, x0 * y1 + x1 * y0 + x1 * y2 + x2 * y1 + x2 * y2,
     x0 * y2 + x1 * y1 + x2 * y0 + x2 * y2]

/-- The image, thirty-two words: `x`, `y`, `x + y`, `x · y` at `2..5`; the `SET` immediate at `6`;
the `DEREF` pointer `g^8` at `7`, its target `g²·g³` (the return address of `pc = g^3`) at `8`,
its local cell at `9`; the `JUMP` cells `c = 1`, `d = g^6`, `f = 1` at `10..12`; the nine
`BLAKE2S` cells at `16..24`; zero elsewhere. -/
def memTable : Array (Vector K 3) :=
  #[#v[0, 0, 0], #v[0, 0, 0],
    #v[x0, x1, x2], #v[y0, y1, y2], #v[x0 + y0, x1 + y1, x2 + y2], xyLanes,
    #v[7, 8, 9],
    #v[gpow 8, 0, 0], #v[g ^ 2 * gpow 3, 0, 0], #v[5, 6, 7],
    #v[1, 0, 0], #v[gpow 6, 0, 0], #v[1, 0, 0],
    #v[0, 0, 0], #v[0, 0, 0], #v[0, 0, 0],
    cell rustM0, cell rustM1, cell rustM2, cell rustM3, cell rustCv0, cell rustCv1,
    cell rustOut0, cell rustOut1, cell rustMd,
    #v[0, 0, 0], #v[0, 0, 0], #v[0, 0, 0], #v[0, 0, 0], #v[0, 0, 0], #v[0, 0, 0], #v[0, 0, 0]]

/-- The program, eight slots: one instruction per opcode, in frame `fp = 1`, then two fillers,
the last the sentinel. -/
def progTable : Array (Vector K 8) :=
  #[entry (.xor (gpow 2) (gpow 3) (gpow 4)),
    entry (.mulNative (gpow 2) (gpow 3) (gpow 5)),
    entry (.setConstant (gpow 6) (E.ofLimbs 7 8 9)),
    entry (.deref (gpow 7) 1 (gpow 9) .pc),
    entry (.jump (gpow 10) (gpow 11) (gpow 12)),
    entry (.blake2s ![gpow 16, gpow 17, gpow 18, gpow 19] (gpow 20) (gpow 22) (gpow 24)),
    entry (.xor 1 1 1), entry (.xor 1 1 1)]

/-- The prover data, its two tables told apart by arity so that the kernel never compares
names (as in the Layer 5 tests). -/
def tabData : ProverData K := fun _ n ↦
  match n with
  | 3 => memTable
  | 8 => progTable
  | _ => #[]

theorem memRows_size : (memRows tabData).size = 32 := rfl
theorem bytecodeRows_size : (bytecodeRows tabData).size = 8 := rfl

theorem mem_logSize : (imageOf tabData).1 = 5 := by
  show min (Nat.log 2 (memRows tabData).size) maxLogMem = 5
  rw [memRows_size, show (32 : ℕ) = 2 ^ 5 by decide, Nat.log_pow (by norm_num)]
  decide

theorem prog_logSize : (programOf tabData).logSize = 3 := by
  show min (Nat.log 2 (bytecodeRows tabData).size) maxLogBytecode = 3
  rw [bytecodeRows_size, show (8 : ℕ) = 2 ^ 3 by decide, Nat.log_pow (by norm_num)]
  decide

theorem tabData_wellShaped : WellShapedData tabData where
  memRows_size := by rw [mem_logSize, memRows_size]; decide
  bytecodeRows_size := by rw [prog_logSize, bytecodeRows_size]; decide

/-- On a well-shaped thirty-two-word data, the word at `g^k` is row `k` of the image, as
limbs. -/
theorem readAt {data : ProverData K} (hlog : (imageOf data).1 = 5) (hws : WellShapedData data)
    (k : ℕ) (v : Vector K 3) (hk : k < 32 := by decide)
    (hv : (memRows data)[k]'(by rw [hws.memRows_size, hlog]; exact hk) = v := by decide +kernel) :
    (imageOf data).2.read (gpow k) = some (E.ofLimbs v[0] v[1] v[2]) := by
  have hk' : k < 2 ^ (imageOf data).1 := by rw [hlog]; omega
  rw [show gpow k = gpow ((⟨k, hk'⟩ : Fin (2 ^ (imageOf data).1)) : ℕ) from rfl,
    MemImage.read_gpow (by rw [hlog]; decide), imageOf_apply hws _ hv]

/-- The word at `g^k` of the fixture's image. -/
theorem read_at (k : ℕ) (v : Vector K 3) (hk : k < 32 := by decide)
    (hv : (memRows tabData)[k]'(by rw [memRows_size]; exact hk) = v := by decide +kernel) :
    (imageOf tabData).2.read (gpow k) = some (E.ofLimbs v[0] v[1] v[2]) :=
  readAt mem_logSize tabData_wellShaped k v hk hv

/-- `read_at` with the word's three limbs spelled out, for the kernel fixtures. -/
theorem read_lit (k : ℕ) (a b c : K) (hk : k < 32 := by decide)
    (hv : (memRows tabData)[k]'(by rw [memRows_size]; exact hk) = #v[a, b, c] :=
      by decide +kernel) :
    (imageOf tabData).2.read (gpow k) = some (E.ofLimbs a b c) :=
  read_at k #v[a, b, c] hk hv

/-- The instruction at `g^i` is row `i` of the program, decoded. -/
theorem fetch_at (i : ℕ) (ins : Instr) (hi : i < 8 := by decide)
    (hd : decode ((bytecodeRows tabData)[i]'(by rw [bytecodeRows_size]; exact hi)) = some ins :=
      by decide +kernel) :
    (programOf tabData).fetch (gpow i) = some ins := by
  have hi' : i < 2 ^ (programOf tabData).logSize := by rw [prog_logSize]; omega
  rw [show gpow i = gpow ((⟨i, hi'⟩ : Fin (2 ^ (programOf tabData).logSize)) : ℕ) from rfl,
    Program.fetch_gpow, programOf_code tabData_wellShaped _ hd]

/-! ## `XOR` -/

/-- The honest `XOR` row at `pc = g^0`, `fp = 1`: operands `g^2, g^3, g^4`, the words `x`, `y`. -/
def xorRow : XorRow K :=
  ⟨gpow 0, 1, gpow 2, gpow 3, gpow 4, #v[x0, x1, x2], #v[y0, y1, y2], 1, 1, 1, 1⟩

theorem xor_honest : xorTable.ProverAssumptions xorRow tabData default := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fetch_at 0 _
  · show (imageOf tabData).2.read (1 * gpow 2) = some (E.ofLimbs x0 x1 x2)
    rw [one_mul]; exact read_at 2 #v[x0, x1, x2]
  · show (imageOf tabData).2.read (1 * gpow 3) = some (E.ofLimbs y0 y1 y2)
    rw [one_mul]; exact read_at 3 #v[y0, y1, y2]
  · show (imageOf tabData).2.read (1 * gpow 4) = some (E.ofLimbs (x0 + y0) (x1 + y1) (x2 + y2))
    rw [one_mul]; exact read_at 4 #v[x0 + y0, x1 + y1, x2 + y2]

/-- The honest row's environment: no local witnesses, the fixture's tables, no hints. -/
def xorEnv : ProverEnvironment K := ⟨⟨fun _ ↦ 0, tabData⟩, default⟩

/-- The row is accepted by `xorTable.completeness`: the constraints of `main` hold on it (the
four pulls' guarantees; there is no assertion). -/
example : ConstraintsHold.Completeness xorEnv ((xorTable.main (const xorRow)).operations 0) :=
  (xorTable.completeness 0 xorEnv (const xorRow)
    (by simp only [circuit_norm, xorTable, memRead, bytecodeRead, -BitVec.reduceNeg])
    xorRow ProvableType.eval_const_prover xor_honest).1

/-- `Spec` on the honest row: the machine steps from `(1, 1)` to `(g, 1)`. -/
example : xorTable.Spec xorRow ⟨g * gpow 0, 1⟩ tabData := by
  show step (programOf tabData) (imageOf tabData).2 ⟨gpow 0, 1⟩ = some ⟨g * gpow 0, 1⟩
  rw [step_of_fetch_eq_some (r := ⟨gpow 0, 1⟩) (fetch_at 0 (.xor (gpow 2) (gpow 3) (gpow 4)))]
  simp only [execute, one_mul, read_at 2 #v[x0, x1, x2], read_at 3 #v[y0, y1, y2],
    read_at 4 #v[x0 + y0, x1 + y1, x2 + y2]]
  decide +kernel

/-- A wrong result limb is rejected: the result read is no read of the image. -/
example : ¬ MemPull.Guarantees ⟨1 * gpow 4, 1, #v[x0 + y0 + 1, x1 + y1, x2 + y2]⟩ tabData := by
  show ¬ (imageOf tabData).2.read (1 * gpow 4) = some (E.ofLimbs _ _ _)
  rw [one_mul, read_at 4 #v[x0 + y0, x1 + y1, x2 + y2]]
  decide +kernel

/-! ## `MUL_NATIVE` -/

/-- The twelve-product coordinates of the Rust operands are the Rust product (acceptance
test 9). -/
example : E.ofLimbs xyLanes[0] xyLanes[1] xyLanes[2] = mulXY := by decide +kernel

/-- The honest `MUL_NATIVE` row at `pc = g^1`. -/
def mulRow : MulRow K :=
  ⟨gpow 1, 1, gpow 2, gpow 3, gpow 5, #v[x0, x1, x2], #v[y0, y1, y2], 1, 1, 1, 1⟩

theorem mul_honest : mulTable.ProverAssumptions mulRow tabData default := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fetch_at 1 _
  · show (imageOf tabData).2.read (1 * gpow 2) = some (E.ofLimbs x0 x1 x2)
    rw [one_mul]; exact read_at 2 #v[x0, x1, x2]
  · show (imageOf tabData).2.read (1 * gpow 3) = some (E.ofLimbs y0 y1 y2)
    rw [one_mul]; exact read_at 3 #v[y0, y1, y2]
  · show (imageOf tabData).2.read (1 * gpow 5) = some (E.ofLimbs xyLanes[0] xyLanes[1] xyLanes[2])
    rw [one_mul]; exact read_at 5 xyLanes

/-- `Spec` on the honest row, through the product of the Rust vectors. -/
example : mulTable.Spec mulRow ⟨g * gpow 1, 1⟩ tabData := by
  show step (programOf tabData) (imageOf tabData).2 ⟨gpow 1, 1⟩ = some ⟨g * gpow 1, 1⟩
  rw [step_of_fetch_eq_some (r := ⟨gpow 1, 1⟩) (fetch_at 1 (.mulNative (gpow 2) (gpow 3) (gpow 5)))]
  simp only [execute, one_mul, read_at 2 #v[x0, x1, x2], read_at 3 #v[y0, y1, y2],
    read_at 5 xyLanes]
  decide +kernel

/-- A wrong product limb is rejected. -/
example : ¬ MemPull.Guarantees ⟨1 * gpow 5, 1, #v[xyLanes[0], xyLanes[1] + 1, xyLanes[2]]⟩
    tabData := by
  show ¬ (imageOf tabData).2.read (1 * gpow 5) = some (E.ofLimbs _ _ _)
  rw [one_mul, read_at 5 xyLanes]
  decide +kernel

/-! ## `SET_CONSTANT` -/

/-- The honest `SET_CONSTANT` row at `pc = g^2`: the immediate `7 + 8·y + 9·y²` at `g^6`. -/
def setRow : SetRow K := ⟨gpow 2, 1, gpow 6, #v[7, 8, 9], 1, 1⟩

theorem set_honest : setTable.ProverAssumptions setRow tabData default := by
  refine ⟨?_, ?_⟩
  · exact fetch_at 2 _
  · show (imageOf tabData).2.read (1 * gpow 6) = some (E.ofLimbs 7 8 9)
    rw [one_mul]; exact read_at 6 #v[7, 8, 9]

example : setTable.Spec setRow ⟨g * gpow 2, 1⟩ tabData := by
  show step (programOf tabData) (imageOf tabData).2 ⟨gpow 2, 1⟩ = some ⟨g * gpow 2, 1⟩
  rw [step_of_fetch_eq_some (r := ⟨gpow 2, 1⟩) (fetch_at 2 (.setConstant (gpow 6) (E.ofLimbs 7 8 9)))]
  simp only [execute, one_mul, read_at 6 #v[7, 8, 9]]
  decide +kernel

/-- A wrong immediate limb is rejected. -/
example : ¬ MemPull.Guarantees ⟨1 * gpow 6, 1, #v[7, 8, 10]⟩ tabData := by
  show ¬ (imageOf tabData).2.read (1 * gpow 6) = some (E.ofLimbs _ _ _)
  rw [one_mul, read_at 6 #v[7, 8, 9]]
  decide +kernel

/-! ## `DEREF` -/

/-- The honest `DEREF` row at `pc = g^3` in `pc` mode (`f_pc = 1`, `f_fp = 0`): pointer `g^8`
at `g^7`, local cell `g^9`, target `g^8 · 1` holding `g² · g^3`. -/
def derefRow : DerefRow K :=
  ⟨gpow 3, 1, gpow 7, 1, gpow 9, 1, 0, gpow 8, #v[5, 6, 7], 1, 1, 1, 1⟩

theorem deref_honest : derefTable.ProverAssumptions derefRow tabData default := by
  refine ⟨.pc, ?_, rfl, ?_, ?_, ?_⟩
  · exact fetch_at 3 _
  · show (imageOf tabData).2.read (1 * gpow 7) = some (E.ofLimbs (gpow 8) 0 0)
    rw [one_mul]; exact read_at 7 #v[gpow 8, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 9) = some (E.ofLimbs 5 6 7)
    rw [one_mul]; exact read_at 9 #v[5, 6, 7]
  · -- The target: `f̄ = 1 + 1 + 0`, so the coordinates are `(g² · pc, 0, 0)` in the kernel.
    show (imageOf tabData).2.read (gpow 8 * 1) = some (E.ofLimbs
      ((1 + 1 + 0) * 5 + 1 * (g ^ 2 * gpow 3) + 0 * 1) ((1 + 1 + 0) * 6) ((1 + 1 + 0) * 7))
    rw [mul_one, read_at 8 #v[g ^ 2 * gpow 3, 0, 0]]
    decide +kernel

example : derefTable.Spec derefRow ⟨g * gpow 3, 1⟩ tabData := by
  show step (programOf tabData) (imageOf tabData).2 ⟨gpow 3, 1⟩ = some ⟨g * gpow 3, 1⟩
  rw [step_of_fetch_eq_some (r := ⟨gpow 3, 1⟩) (fetch_at 3 (.deref (gpow 7) 1 (gpow 9) .pc))]
  simp only [execute, one_mul, mul_one, read_lit 7 (gpow 8) 0 0, Option.bind_eq_bind,
    Option.bind_some, guard, isInK_ofLimbs, ite_true, limb_ofLimbs, Matrix.cons_val_zero,
    read_lit 9 5 6 7, read_lit 8 (g ^ 2 * gpow 3) 0 0, derefSource, ofK_eq_ofLimbs]
  decide +kernel

/-- The flag pair `(1, 1)` is no store mode: its bytecode tuple decodes to nothing, so the row
cannot pull it, at this counter or any other (acceptance test 18). -/
example (pc : K) :
    ¬ BytecodePull.Guarantees ⟨pc, 1, Opcode.deref.code, #v[gpow 7, 1, gpow 9, 1, 1, 0, 0]⟩
      tabData := by
  rintro ⟨ins, -, hdec⟩
  have h : decode (#v[Opcode.deref.code] ++ #v[gpow 7, 1, gpow 9, 1, 1, 0, 0]) = none := by
    decide +kernel
  exact nomatch h.symm.trans hdec

/-! ## `JUMP` -/

/-- The honest `JUMP` row at `pc = g^4`, taken: `c = 1`, `d = g^6`, `f = 1`. -/
def jumpRow : JumpRow K := ⟨gpow 4, 1, gpow 10, gpow 11, gpow 12, 1, gpow 6, 1, 1, 1, 1, 1⟩

theorem jump_honest : jumpTable.ProverAssumptions jumpRow tabData default := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fetch_at 4 _
  · show (imageOf tabData).2.read (1 * gpow 10) = some (E.ofLimbs 1 0 0)
    rw [one_mul]; exact read_at 10 #v[1, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 11) = some (E.ofLimbs (gpow 6) 0 0)
    rw [one_mul]; exact read_at 11 #v[gpow 6, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 12) = some (E.ofLimbs 1 0 0)
    rw [one_mul]; exact read_at 12 #v[1, 0, 0]

/-- The honest witnesses of the row, `w = 1⁻¹ = 1` and `b = 1`, satisfy the two residuals
(`flags_complete` at `v_cond = 1`, in the kernel). -/
example : (1 : K) + 1 * (1 : K)⁻¹ = 0 ∧ (1 : K) * (1 + 1) = 0 := by decide +kernel

/-- `Spec` on the honest row: the branch is taken, to `(g^6, 1)`. -/
example : jumpTable.Spec jumpRow ⟨gpow 6, 1⟩ tabData := by
  show step (programOf tabData) (imageOf tabData).2 ⟨gpow 4, 1⟩ = some ⟨gpow 6, 1⟩
  rw [step_of_fetch_eq_some (r := ⟨gpow 4, 1⟩) (fetch_at 4 (.jump (gpow 10) (gpow 11) (gpow 12)))]
  simp only [execute, one_mul, read_at 10 #v[1, 0, 0], read_at 11 #v[gpow 6, 0, 0],
    read_at 12 #v[1, 0, 0]]
  decide +kernel

/-- The pushed successor of the honest row is the step's: `b = 1` selects `(d, f)`. -/
example : (1 : K) * gpow 6 + 1 * (g * gpow 4) + g * gpow 4 = gpow 6 ∧
    (1 : K) * 1 + 1 * 1 + 1 = 1 := by
  decide +kernel

/-- The wrong flag row `b = 1, v_cond = 0` fails the first residual for every inverse `w`
(acceptance test 8): booleanity of `b` alone would have admitted it. -/
example (w : K) : (1 : K) + 0 * w ≠ 0 := by
  rw [zero_mul, add_zero]; exact one_ne_zero

/-- With `v_cond = 0` the residuals force `b = 0`, whatever `w`. -/
example (w b : K) (h1 : b + 0 * w = 0) (h2 : 0 * (b + 1) = 0) : b = 0 := by
  simpa using flags_sound h1 h2

/-! ## `BLAKE2S` -/

/-- The honest `BLAKE2S` row at `pc = g^5`: the executor's cells at `g^16 … g^24`. -/
def blake2sRow : Blake2sRow K :=
  ⟨gpow 5, 1, gpow 16, gpow 17, gpow 18, gpow 19, gpow 20, gpow 22, gpow 24,
    rustM0, rustM1, rustM2, rustM3, rustOut0, rustOut1, rustCv0, rustCv1, rustMd,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

/-- `g · g^k = g^(k + 1)`, oriented for `simp`. -/
theorem g_mul_gpow (k : ℕ) : g * gpow k = gpow (k + 1) := (gpow_succ k).symm

/-- A canonical cell read of the fixture, at `1 · g^k`. -/
theorem read_cell (k : ℕ) (c : Vector K 2) (hk : k < 32 := by decide)
    (hv : (memRows tabData)[k]'(by rw [memRows_size]; exact hk) = cell c := by decide +kernel) :
    (imageOf tabData).2.read (1 * gpow k) = some (cellOf c) := by
  rw [one_mul]; exact read_at k (cell c) hk hv

theorem blake2s_honest : blake2sTable.ProverAssumptions blake2sRow tabData default := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fetch_at 5 _
  · exact read_cell 16 rustM0
  · exact read_cell 17 rustM1
  · exact read_cell 18 rustM2
  · exact read_cell 19 rustM3
  · exact read_cell 20 rustCv0
  · show (imageOf tabData).2.read (1 * (g * gpow 20)) = some (cellOf rustCv1)
    rw [g_mul_gpow]; exact read_cell 21 rustCv1
  · exact read_cell 22 rustOut0
  · show (imageOf tabData).2.read (1 * (g * gpow 22)) = some (cellOf rustOut1)
    rw [g_mul_gpow]; exact read_cell 23 rustOut1
  · exact read_cell 24 rustMd

/-- The named assumption holds of the honest row: the executor's cells compress. -/
theorem blake2s_relation : Blake2sRelation blake2sRow := by
  show CompressCells _ _ _ _ _ _
  decide +kernel

/-- `Spec` on the honest row. -/
example : blake2sTable.Spec blake2sRow ⟨g * gpow 5, 1⟩ tabData := by
  show step (programOf tabData) (imageOf tabData).2 ⟨gpow 5, 1⟩ = some ⟨g * gpow 5, 1⟩
  rw [step_of_fetch_eq_some (r := ⟨gpow 5, 1⟩)
    (fetch_at 5 (.blake2s ![gpow 16, gpow 17, gpow 18, gpow 19] (gpow 20) (gpow 22) (gpow 24)))]
  simp only [execute, one_mul, g_mul_gpow, Matrix.cons_val, Fin.isValue, read_at 16 (cell rustM0),
    read_at 17 (cell rustM1), read_at 18 (cell rustM2), read_at 19 (cell rustM3),
    read_at 20 (cell rustCv0), read_at 21 (cell rustCv1), read_at 22 (cell rustOut0),
    read_at 23 (cell rustOut1), read_at 24 (cell rustMd), Option.bind_eq_bind, Option.bind_some]
  decide +kernel

/-- A non-canonical cell is rejected (acceptance test 12): an image whose second output cell has
a nonzero top limb does not balance the row's canonical read of it. -/
def badData : ProverData K := fun _ n ↦
  match n with
  | 3 => memTable.set! 23 #v[rustOut1[0], rustOut1[1], 1]
  | 8 => progTable
  | _ => #[]

theorem bad_memRows_size : (memRows badData).size = 32 := rfl

theorem bad_logSize : (imageOf badData).1 = 5 := by
  show min (Nat.log 2 (memRows badData).size) maxLogMem = 5
  rw [bad_memRows_size, show (32 : ℕ) = 2 ^ 5 by decide, Nat.log_pow (by norm_num)]
  decide

theorem badData_wellShaped : WellShapedData badData where
  memRows_size := by rw [bad_logSize, bad_memRows_size]; decide
  bytecodeRows_size := by
    show (bytecodeRows badData).size = 2 ^ min (Nat.log 2 (bytecodeRows badData).size)
      maxLogBytecode
    rw [show (bytecodeRows badData).size = 8 from rfl, show (8 : ℕ) = 2 ^ 3 by decide,
      Nat.log_pow (by norm_num)]
    decide

example : ¬ MemPull.Guarantees ⟨1 * (g * gpow 22), 1, #v[rustOut1[0], rustOut1[1], 0]⟩
    badData := by
  show ¬ (imageOf badData).2.read (1 * (g * gpow 22)) = some (E.ofLimbs _ _ _)
  rw [one_mul, g_mul_gpow, readAt bad_logSize badData_wellShaped 23 #v[rustOut1[0], rustOut1[1], 1]]
  decide +kernel

end LeanerVMTests.Arithmetization.Tables
