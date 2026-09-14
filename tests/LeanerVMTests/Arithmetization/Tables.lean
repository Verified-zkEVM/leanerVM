import LeanerVM.Arithmetization.Tables.Xor
import LeanerVM.Arithmetization.Tables.MulNative
import LeanerVM.Arithmetization.Tables.SetConstant
import LeanerVM.Arithmetization.Tables.Deref
import LeanerVM.Arithmetization.Tables.Jump
import LeanerVM.Arithmetization.Tables.Blake2s
import Clean.Circuit.WitnessGeneration

/-!
# Layer 6 tests: the six opcode tables

A plain file, like the modules it tests: the fixtures decide `E` arithmetic and `Regs`
equalities in the kernel. One prover data serves every table: a thirty-two-word image
(`κ = 5`) and a sixteen-slot program with one instruction per opcode, a `DEREF` in each of the
three store modes and a `JUMP` on each branch, both read through `imageOf`/`programOf` at
literal indices as in the Layer 5 tests.

For each table: the honest row is bound (`*RowBindings`), satisfies its functional
specification (`*Spec`, with Layer 3's `step` decided in the kernel), is accepted by `main`
(its constraints hold in its honest environment, through `completeness`: `*Row_complete`), and
`main` returns the pushed successor (`*_output`). The `JUMP` rows, taken and untaken, are
pushed through `completeness` in `jumpEnv`, whose two witness slots are what the witness
programs compute (`jump_env_iff`); Clean's array generator `Circuit.witgen` computes the same
two values (`#guard`, compiled). The `DEREF` rows cover the three modes.

Rejections use actual rows and the tables' own theorems: the review's counterexamples to the
old step-only contract (an `XOR` row at the `SET` instruction; a `DEREF` row with the flag pair
`(1, 1)`) satisfy `step` from their registers and fail their bindings; a changed input limb
(`XOR`, `MUL_NATIVE`), a changed immediate (`SET_CONSTANT`), and a non-canonical image cell
(`BLAKE2S`, acceptance test 12) fail the constraints `main` emits in every environment over
the data (`*_reads_of_constraints`, `blake2s_bindings_of_constraints`); the wrong witness
`b = 1` at `v_cond = 0` fails the first residual (`jump_residuals_of_constraints`, acceptance
test 8). The `BLAKE2S` boundary: a bound row whose output cell is a wrong but canonical word,
consistently in row and image, is locally complete and fails `Blake2sRelation` and
`Blake2sSpec`, the failure Flock enforces.

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

/-- The image, thirty-two words: `x`, `y`, `x + y`, `x · y` at `2..5`; the `SET` immediate at
`6`; the `pc`-mode `DEREF` pointer `g^8` at `7`, its target `g²·g³` (the return address of
`pc = g^3`) at `8`, its local cell at `9`; the `JUMP` cells `c = 1`, `d = g^6`, `f = 1` at
`10..12` and the untaken condition `c = 0` at `13`; the nine `BLAKE2S` cells at `16..24`; the
`cell`-mode `DEREF` pointer `g^26` at `25`, its target at `26` holding the local word at `27`;
the `fp`-mode `DEREF` pointer `g^29` at `28`, its target at `29` holding `fp = 1`, its local cell
at `30`; zero elsewhere. -/
def memTable : Array (Vector K 3) :=
  #[#v[0, 0, 0], #v[0, 0, 0],
    #v[x0, x1, x2], #v[y0, y1, y2], #v[x0 + y0, x1 + y1, x2 + y2], xyLanes,
    #v[7, 8, 9],
    #v[gpow 8, 0, 0], #v[g ^ 2 * gpow 3, 0, 0], #v[5, 6, 7],
    #v[1, 0, 0], #v[gpow 6, 0, 0], #v[1, 0, 0],
    #v[0, 0, 0], #v[0, 0, 0], #v[0, 0, 0],
    cell rustM0, cell rustM1, cell rustM2, cell rustM3, cell rustCv0, cell rustCv1,
    cell rustOut0, cell rustOut1, cell rustMd,
    #v[gpow 26, 0, 0], #v[3, 4, 5], #v[3, 4, 5],
    #v[gpow 29, 0, 0], #v[1, 0, 0], #v[9, 9, 9],
    #v[0, 0, 0]]

/-- The program, sixteen slots: one instruction per opcode in frame `fp = 1`, a `DEREF` in
`cell` mode and one in `fp` mode, an untaken `JUMP`, then fillers, the last the sentinel. -/
def progTable : Array (Vector K 8) :=
  #[entry (.xor (gpow 2) (gpow 3) (gpow 4)),
    entry (.mulNative (gpow 2) (gpow 3) (gpow 5)),
    entry (.setConstant (gpow 6) (E.ofLimbs 7 8 9)),
    entry (.deref (gpow 7) 1 (gpow 9) .pc),
    entry (.jump (gpow 10) (gpow 11) (gpow 12)),
    entry (.blake2s ![gpow 16, gpow 17, gpow 18, gpow 19] (gpow 20) (gpow 22) (gpow 24)),
    entry (.deref (gpow 25) 1 (gpow 27) .cell),
    entry (.deref (gpow 28) 1 (gpow 30) .fp),
    entry (.jump (gpow 13) (gpow 11) (gpow 12)),
    entry (.xor 1 1 1), entry (.xor 1 1 1), entry (.xor 1 1 1), entry (.xor 1 1 1),
    entry (.xor 1 1 1), entry (.xor 1 1 1), entry (.xor 1 1 1)]

/-- The prover data of an image over the fixture's program, its two tables told apart by arity
so that the kernel never compares names (as in the Layer 5 tests). -/
def dataOf (mem : Array (Vector K 3)) : ProverData K := fun _ n ↦
  match n with
  | 3 => mem
  | 8 => progTable
  | _ => #[]

/-- The fixture's prover data. -/
def tabData : ProverData K := dataOf memTable

theorem dataOf_logSize {mem : Array (Vector K 3)} (h : mem.size = 32) :
    (imageOf (dataOf mem)).1 = 5 := by
  show min (Nat.log 2 (memRows (dataOf mem)).size) maxLogMem = 5
  rw [show memRows (dataOf mem) = mem from rfl, h, show (32 : ℕ) = 2 ^ 5 by decide,
    Nat.log_pow (by norm_num)]
  decide

theorem prog_logSize (mem : Array (Vector K 3)) : (programOf (dataOf mem)).logSize = 4 := by
  show min (Nat.log 2 (bytecodeRows (dataOf mem)).size) maxLogBytecode = 4
  rw [show (bytecodeRows (dataOf mem)).size = 16 from rfl, show (16 : ℕ) = 2 ^ 4 by decide,
    Nat.log_pow (by norm_num)]
  decide

theorem dataOf_wellShaped {mem : Array (Vector K 3)} (h : mem.size = 32) :
    WellShapedData (dataOf mem) where
  memRows_size := by rw [dataOf_logSize h]; exact h
  bytecodeRows_size := by rw [prog_logSize]; rfl

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
    (hv : memTable[k]'(by rw [show memTable.size = 32 from rfl]; exact hk) = v :=
      by decide +kernel) :
    (imageOf tabData).2.read (gpow k) = some (E.ofLimbs v[0] v[1] v[2]) :=
  readAt (dataOf_logSize rfl) (dataOf_wellShaped rfl) k v hk hv

/-- `read_at` with the word's three limbs spelled out, for the kernel fixtures. -/
theorem read_lit (k : ℕ) (a b c : K) (hk : k < 32 := by decide)
    (hv : memTable[k]'(by rw [show memTable.size = 32 from rfl]; exact hk) = #v[a, b, c] :=
      by decide +kernel) :
    (imageOf tabData).2.read (gpow k) = some (E.ofLimbs a b c) :=
  read_at k #v[a, b, c] hk hv

/-- On any thirty-two-word image over the fixture's program, the instruction at `g^i` is row
`i` of the program, decoded. -/
theorem fetchAt (mem : Array (Vector K 3)) (h : mem.size = 32) (i : ℕ) (ins : Instr)
    (hi : i < 16 := by decide)
    (hd : decode (progTable[i]'(by rw [show progTable.size = 16 from rfl]; exact hi)) = some ins :=
      by decide +kernel) :
    (programOf (dataOf mem)).fetch (gpow i) = some ins := by
  have hi' : i < 2 ^ (programOf (dataOf mem)).logSize := by rw [prog_logSize]; omega
  rw [show gpow i = gpow ((⟨i, hi'⟩ : Fin (2 ^ (programOf (dataOf mem)).logSize)) : ℕ) from rfl,
    Program.fetch_gpow, programOf_code (dataOf_wellShaped h) ⟨i, hi'⟩ hd]

/-- The instruction at `g^i` of the fixture's program, decoded. -/
theorem fetch_at (i : ℕ) (ins : Instr) (hi : i < 16 := by decide)
    (hd : decode (progTable[i]'(by rw [show progTable.size = 16 from rfl]; exact hi)) = some ins :=
      by decide +kernel) :
    (programOf tabData).fetch (gpow i) = some ins :=
  fetchAt memTable rfl i ins hi hd

/-- `g · g^k = g^(k + 1)`, oriented for `simp`. -/
theorem g_mul_gpow (k : ℕ) : g * gpow k = gpow (k + 1) := (gpow_succ k).symm

/-! ## `XOR` -/

/-- The honest `XOR` row at `pc = g^0`, `fp = 1`: operands `g^2, g^3, g^4`, the words `x`, `y`. -/
def xorRow : XorRow K :=
  ⟨gpow 0, 1, gpow 2, gpow 3, gpow 4, #v[x0, x1, x2], #v[y0, y1, y2], 1, 1, 1, 1⟩

/-- The honest row is bound: the instruction and the two operand words are the fixture's. -/
theorem xor_bindings : XorRowBindings xorRow tabData := by
  refine ⟨fetch_at 0 _, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 2) = some (E.ofLimbs x0 x1 x2)
    rw [one_mul]; exact read_at 2 #v[x0, x1, x2]
  · show (imageOf tabData).2.read (1 * gpow 3) = some (E.ofLimbs y0 y1 y2)
    rw [one_mul]; exact read_at 3 #v[y0, y1, y2]

/-- `XorSpec` on the honest row: bound, and the machine steps from `(1, 1)` to `(g, 1)`. -/
theorem xor_spec : XorSpec xorRow ⟨g * gpow 0, 1⟩ tabData :=
  ⟨xor_bindings, by
    show step (programOf tabData) (imageOf tabData).2 ⟨gpow 0, 1⟩ = some ⟨g * gpow 0, 1⟩
    rw [step_of_fetch_eq_some (r := ⟨gpow 0, 1⟩) (fetch_at 0 (.xor (gpow 2) (gpow 3) (gpow 4)))]
    simp only [execute, one_mul, read_at 2 #v[x0, x1, x2], read_at 3 #v[y0, y1, y2],
      read_at 4 #v[x0 + y0, x1 + y1, x2 + y2]]
    decide +kernel⟩

/-- The row is accepted by `main`: its constraints hold in the row environment over the
fixture (through `completeness`). -/
example : ConstraintsHold.Completeness (rowEnv tabData) ((xorTable.main (const xorRow)).operations 0) :=
  xorRow_complete ⟨_, xor_spec⟩

/-- The valid step alone yields a satisfying row (`xor_step_complete`): no assumption on the
row, the honest prover builds it. -/
example : ConstraintsHold.Completeness (rowEnv tabData)
    ((xorTable.main (const (xorRowOf tabData (gpow 0) 1 (gpow 2) (gpow 3) (gpow 4) 1 1 1 1))).operations 0) :=
  xor_step_complete (fetch_at 0 _) xor_spec.2 1 1 1 1

/-- `main` returns the pushed successor `(g, 1)`. -/
example : eval (rowEnv tabData).toEnvironment ((xorTable.main (const xorRow)).output 0) =
    ⟨g * gpow 0, 1⟩ := by
  simp only [xor_output, ProvableType.eval_const, xorRow]

/-- The step admits a row with the honest registers and operands (`xor_row_exists`). -/
example : ∃ vA vB, XorSpec ⟨gpow 0, 1, gpow 2, gpow 3, gpow 4, vA, vB, 1, 1, 1, 1⟩
    ⟨g * gpow 0, 1⟩ tabData :=
  xor_row_exists (fetch_at 0 _) xor_spec.2 1 1 1 1

/-- The review's counterexample to the old step-only contract: an alleged `XOR` row at the
`SET` instruction with operands `0` satisfies `step` from its registers. -/
def bogusXor : XorRow K :=
  { xorRow with pc := gpow 2, oA := 0, oB := 0, oC := 0, vA := #v[0, 0, 0] }

example : step (programOf tabData) (imageOf tabData).2 ⟨bogusXor.pc, bogusXor.fp⟩ =
    some ⟨g * gpow 2, 1⟩ := by
  show step (programOf tabData) (imageOf tabData).2 ⟨gpow 2, 1⟩ = some ⟨g * gpow 2, 1⟩
  rw [step_of_fetch_eq_some (r := ⟨gpow 2, 1⟩)
    (fetch_at 2 (.setConstant (gpow 6) (E.ofLimbs 7 8 9)))]
  simp only [execute, one_mul, read_at 6 #v[7, 8, 9]]
  decide +kernel

/-- …and fails `XorSpec` for every successor: the instruction at `g^2` is no `XOR`. -/
example (next : Regs K) : ¬ XorSpec bogusXor next tabData := by
  rintro ⟨⟨hfetch, -, -⟩, -⟩
  rw [show bogusXor.pc = gpow 2 from rfl,
    fetch_at 2 (.setConstant (gpow 6) (E.ofLimbs 7 8 9))] at hfetch
  cases hfetch

/-- A changed input limb: `step` from the registers is unchanged, the bindings fail. -/
def xorRow' : XorRow K := { xorRow with vA := #v[x0 + 1, x1, x2] }

example (next : Regs K) : ¬ XorSpec xorRow' next tabData := by
  rintro ⟨⟨-, hA, -⟩, -⟩
  rw [show xorRow'.fp * xorRow'.oA = 1 * gpow 2 from rfl, one_mul, read_at 2 #v[x0, x1, x2]] at hA
  exact absurd (Option.some.inj hA) (by decide +kernel)

/-- …so the constraints `main` emits on it fail in every environment over the fixture: its
second pull is no read of the image. -/
example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, tabData⟩ ((xorTable.main (const xorRow')).operations 0) := by
  intro h
  obtain ⟨next, hs⟩ := xor_spec_of_constraints h
  rw [ProvableType.eval_const] at hs
  dsimp only at hs
  obtain ⟨⟨-, hA, -⟩, -⟩ := hs
  rw [show xorRow'.fp * xorRow'.oA = 1 * gpow 2 from rfl, one_mul, read_at 2 #v[x0, x1, x2]] at hA
  exact absurd (Option.some.inj hA) (by decide +kernel)

/-! ## `MUL_NATIVE` -/

/-- The twelve-product coordinates of the Rust operands are the Rust product (acceptance
test 9). -/
example : E.ofLimbs xyLanes[0] xyLanes[1] xyLanes[2] = mulXY := by decide +kernel

/-- The honest `MUL_NATIVE` row at `pc = g^1`. -/
def mulRow : MulRow K :=
  ⟨gpow 1, 1, gpow 2, gpow 3, gpow 5, #v[x0, x1, x2], #v[y0, y1, y2], 1, 1, 1, 1⟩

theorem mul_bindings : MulRowBindings mulRow tabData := by
  refine ⟨fetch_at 1 _, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 2) = some (E.ofLimbs x0 x1 x2)
    rw [one_mul]; exact read_at 2 #v[x0, x1, x2]
  · show (imageOf tabData).2.read (1 * gpow 3) = some (E.ofLimbs y0 y1 y2)
    rw [one_mul]; exact read_at 3 #v[y0, y1, y2]

/-- `MulSpec` on the honest row, through the product of the Rust vectors. -/
theorem mul_spec : MulSpec mulRow ⟨g * gpow 1, 1⟩ tabData :=
  ⟨mul_bindings, by
    show step (programOf tabData) (imageOf tabData).2 ⟨gpow 1, 1⟩ = some ⟨g * gpow 1, 1⟩
    rw [step_of_fetch_eq_some (r := ⟨gpow 1, 1⟩)
      (fetch_at 1 (.mulNative (gpow 2) (gpow 3) (gpow 5)))]
    simp only [execute, one_mul, read_at 2 #v[x0, x1, x2], read_at 3 #v[y0, y1, y2],
      read_at 5 xyLanes]
    decide +kernel⟩

theorem mul_reads : MulRowReads mulRow tabData := (mul_reads_iff _ _).mpr ⟨_, mul_spec⟩

example : ConstraintsHold.Completeness (rowEnv tabData) ((mulTable.main (const mulRow)).operations 0) :=
  mulRow_complete ⟨_, mul_spec⟩

example : eval (rowEnv tabData).toEnvironment ((mulTable.main (const mulRow)).output 0) =
    ⟨g * gpow 1, 1⟩ := by
  simp only [mul_output, ProvableType.eval_const, mulRow]

/-- A changed input limb fails the bindings, and the constraints in every environment. -/
def mulRow' : MulRow K := { mulRow with vB := #v[y0, y1 + 1, y2] }

example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, tabData⟩ ((mulTable.main (const mulRow')).operations 0) := by
  intro h
  have hr := mul_reads_of_constraints h
  rw [ProvableType.eval_const] at hr
  dsimp only at hr
  obtain ⟨-, -, hB, -⟩ := hr
  rw [show mulRow'.fp * mulRow'.oB = 1 * gpow 3 from rfl, one_mul, read_at 3 #v[y0, y1, y2]] at hB
  exact absurd (Option.some.inj hB) (by decide +kernel)

/-! ## `SET_CONSTANT` -/

/-- The honest `SET_CONSTANT` row at `pc = g^2`: the immediate `7 + 8·y + 9·y²` at `g^6`. -/
def setRow : SetRow K := ⟨gpow 2, 1, gpow 6, #v[7, 8, 9], 1, 1⟩

theorem set_bindings : SetRowBindings setRow tabData := fetch_at 2 _

theorem set_spec : SetSpec setRow ⟨g * gpow 2, 1⟩ tabData :=
  ⟨set_bindings, by
    show step (programOf tabData) (imageOf tabData).2 ⟨gpow 2, 1⟩ = some ⟨g * gpow 2, 1⟩
    rw [step_of_fetch_eq_some (r := ⟨gpow 2, 1⟩)
      (fetch_at 2 (.setConstant (gpow 6) (E.ofLimbs 7 8 9)))]
    simp only [execute, one_mul, read_at 6 #v[7, 8, 9]]
    decide +kernel⟩

theorem set_reads : SetRowReads setRow tabData := (set_reads_iff _ _).mpr ⟨_, set_spec⟩

example : ConstraintsHold.Completeness (rowEnv tabData) ((setTable.main (const setRow)).operations 0) :=
  setRow_complete ⟨_, set_spec⟩

example : eval (rowEnv tabData).toEnvironment ((setTable.main (const setRow)).output 0) =
    ⟨g * gpow 2, 1⟩ := by
  simp only [set_output, ProvableType.eval_const, setRow]

/-- A changed immediate limb: the row names an instruction the program does not hold, so its
binding fails and the constraints fail in every environment. -/
def setRow' : SetRow K := { setRow with k := #v[7, 8, 10] }

example (next : Regs K) : ¬ SetSpec setRow' next tabData := by
  rintro ⟨hfetch, -⟩
  unfold SetRowBindings at hfetch
  rw [show setRow'.pc = gpow 2 from rfl, fetch_at 2 (.setConstant (gpow 6) (E.ofLimbs 7 8 9))]
    at hfetch
  simp only [Option.some.injEq, Instr.setConstant.injEq] at hfetch
  exact absurd hfetch.2 (by decide +kernel)

example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, tabData⟩ ((setTable.main (const setRow')).operations 0) := by
  intro h
  have hr := set_reads_of_constraints h
  rw [ProvableType.eval_const] at hr
  dsimp only at hr
  obtain ⟨hfetch, -⟩ := hr
  rw [show setRow'.pc = gpow 2 from rfl, fetch_at 2 (.setConstant (gpow 6) (E.ofLimbs 7 8 9))]
    at hfetch
  simp only [Option.some.injEq, Instr.setConstant.injEq] at hfetch
  exact absurd hfetch.2 (by decide +kernel)

/-! ## `DEREF` -/

/-- The honest `DEREF` row at `pc = g^3` in `pc` mode (`f_pc = 1`, `f_fp = 0`): pointer `g^8`
at `g^7`, local cell `g^9`, target `g^8 · 1` holding `g² · g^3`. -/
def derefRow : DerefRow K :=
  ⟨gpow 3, 1, gpow 7, 1, gpow 9, 1, 0, gpow 8, #v[5, 6, 7], 1, 1, 1, 1⟩

/-- The `cell`-mode row at `pc = g^6`: pointer `g^26` at `g^25`, local cell `g^27`, target
`g^26 · 1` holding the local word. -/
def derefCellRow : DerefRow K :=
  ⟨gpow 6, 1, gpow 25, 1, gpow 27, 0, 0, gpow 26, #v[3, 4, 5], 1, 1, 1, 1⟩

/-- The `fp`-mode row at `pc = g^7`: pointer `g^29` at `g^28`, local cell `g^30` (read, not
stored), target `g^29 · 1` holding `fp = 1`. -/
def derefFpRow : DerefRow K :=
  ⟨gpow 7, 1, gpow 28, 1, gpow 30, 0, 1, gpow 29, #v[9, 9, 9], 1, 1, 1, 1⟩

theorem deref_bindings : DerefRowBindings derefRow tabData := by
  refine ⟨.pc, fetch_at 3 _, rfl, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 7) = some (E.ofLimbs (gpow 8) 0 0)
    rw [one_mul]; exact read_at 7 #v[gpow 8, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 9) = some (E.ofLimbs 5 6 7)
    rw [one_mul]; exact read_at 9 #v[5, 6, 7]

theorem derefCell_bindings : DerefRowBindings derefCellRow tabData := by
  refine ⟨.cell, fetch_at 6 _, rfl, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 25) = some (E.ofLimbs (gpow 26) 0 0)
    rw [one_mul]; exact read_at 25 #v[gpow 26, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 27) = some (E.ofLimbs 3 4 5)
    rw [one_mul]; exact read_at 27 #v[3, 4, 5]

theorem derefFp_bindings : DerefRowBindings derefFpRow tabData := by
  refine ⟨.fp, fetch_at 7 _, rfl, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 28) = some (E.ofLimbs (gpow 29) 0 0)
    rw [one_mul]; exact read_at 28 #v[gpow 29, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 30) = some (E.ofLimbs 9 9 9)
    rw [one_mul]; exact read_at 30 #v[9, 9, 9]

/-- `DerefSpec` in `pc` mode: the target holds the return address `g² · g^3`. -/
theorem deref_spec : DerefSpec derefRow ⟨g * gpow 3, 1⟩ tabData :=
  ⟨deref_bindings, by
    show step (programOf tabData) (imageOf tabData).2 ⟨gpow 3, 1⟩ = some ⟨g * gpow 3, 1⟩
    rw [step_of_fetch_eq_some (r := ⟨gpow 3, 1⟩) (fetch_at 3 (.deref (gpow 7) 1 (gpow 9) .pc))]
    simp only [execute, one_mul, mul_one, read_lit 7 (gpow 8) 0 0, Option.bind_eq_bind,
      Option.bind_some, guard, isInK_ofLimbs, ite_true, limb_ofLimbs, Matrix.cons_val_zero,
      read_lit 9 5 6 7, read_lit 8 (g ^ 2 * gpow 3) 0 0, derefSource, ofK_eq_ofLimbs]
    decide +kernel⟩

/-- `DerefSpec` in `cell` mode: the target holds the local word. -/
theorem derefCell_spec : DerefSpec derefCellRow ⟨g * gpow 6, 1⟩ tabData :=
  ⟨derefCell_bindings, by
    show step (programOf tabData) (imageOf tabData).2 ⟨gpow 6, 1⟩ = some ⟨g * gpow 6, 1⟩
    rw [step_of_fetch_eq_some (r := ⟨gpow 6, 1⟩)
      (fetch_at 6 (.deref (gpow 25) 1 (gpow 27) .cell))]
    simp only [execute, one_mul, mul_one, read_lit 25 (gpow 26) 0 0, Option.bind_eq_bind,
      Option.bind_some, guard, isInK_ofLimbs, ite_true, limb_ofLimbs, Matrix.cons_val_zero,
      read_lit 27 3 4 5, read_lit 26 3 4 5, derefSource]
    decide +kernel⟩

/-- `DerefSpec` in `fp` mode: the target holds `fp = 1`; the local cell is read all the same. -/
theorem derefFp_spec : DerefSpec derefFpRow ⟨g * gpow 7, 1⟩ tabData :=
  ⟨derefFp_bindings, by
    show step (programOf tabData) (imageOf tabData).2 ⟨gpow 7, 1⟩ = some ⟨g * gpow 7, 1⟩
    rw [step_of_fetch_eq_some (r := ⟨gpow 7, 1⟩)
      (fetch_at 7 (.deref (gpow 28) 1 (gpow 30) .fp))]
    simp only [execute, one_mul, mul_one, read_lit 28 (gpow 29) 0 0, Option.bind_eq_bind,
      Option.bind_some, guard, isInK_ofLimbs, ite_true, limb_ofLimbs, Matrix.cons_val_zero,
      read_lit 30 9 9 9, read_lit 29 1 0 0, derefSource, ofK_eq_ofLimbs]
    decide +kernel⟩

theorem deref_reads : DerefRowReads derefRow tabData := (deref_reads_iff _ _).mpr ⟨_, deref_spec⟩

/-- The three rows are accepted by `main`, and `main` returns their pushed successors. -/
example : ConstraintsHold.Completeness (rowEnv tabData)
    ((derefTable.main (const derefRow)).operations 0) :=
  derefRow_complete ⟨_, deref_spec⟩

example : ConstraintsHold.Completeness (rowEnv tabData)
    ((derefTable.main (const derefCellRow)).operations 0) :=
  derefRow_complete ⟨_, derefCell_spec⟩

example : ConstraintsHold.Completeness (rowEnv tabData)
    ((derefTable.main (const derefFpRow)).operations 0) :=
  derefRow_complete ⟨_, derefFp_spec⟩

example : eval (rowEnv tabData).toEnvironment ((derefTable.main (const derefRow)).output 0) =
    ⟨g * gpow 3, 1⟩ := by
  simp only [deref_output, ProvableType.eval_const, derefRow]

example : eval (rowEnv tabData).toEnvironment ((derefTable.main (const derefFpRow)).output 0) =
    ⟨g * gpow 7, 1⟩ := by
  simp only [deref_output, ProvableType.eval_const, derefFpRow]

/-- The review's counterexample to the old contract: the honest row with the flag pair
`(1, 1)` satisfies `step` from its registers (the flags are no input of `step`)… -/
def invalidDeref : DerefRow K := { derefRow with fpc := 1, ffp := 1 }

example : step (programOf tabData) (imageOf tabData).2 ⟨invalidDeref.pc, invalidDeref.fp⟩ =
    some ⟨g * gpow 3, 1⟩ :=
  deref_spec.2

/-- …and fails `DerefSpec` for every successor: `(1, 1)` is no store mode's flags. -/
example (next : Regs K) : ¬ DerefSpec invalidDeref next tabData := by
  rintro ⟨⟨mode, -, hflags, -, -⟩, -⟩
  cases mode <;> exact absurd hflags (by decide +kernel)

/-- The flag pair `(1, 1)` cannot be pulled either: its bytecode tuple decodes to nothing, at
this counter or any other (acceptance test 18). -/
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

/-- The untaken `JUMP` row at `pc = g^8`: `c = 0`, the same `d`, `f`. -/
def jumpRow0 : JumpRow K := ⟨gpow 8, 1, gpow 13, gpow 11, gpow 12, 0, gpow 6, 1, 1, 1, 1, 1⟩

theorem jump_bindings : JumpRowBindings jumpRow tabData := by
  refine ⟨fetch_at 4 _, ?_, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 10) = some (E.ofLimbs 1 0 0)
    rw [one_mul]; exact read_at 10 #v[1, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 11) = some (E.ofLimbs (gpow 6) 0 0)
    rw [one_mul]; exact read_at 11 #v[gpow 6, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 12) = some (E.ofLimbs 1 0 0)
    rw [one_mul]; exact read_at 12 #v[1, 0, 0]

theorem jump0_bindings : JumpRowBindings jumpRow0 tabData := by
  refine ⟨fetch_at 8 _, ?_, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 13) = some (E.ofLimbs 0 0 0)
    rw [one_mul]; exact read_at 13 #v[0, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 11) = some (E.ofLimbs (gpow 6) 0 0)
    rw [one_mul]; exact read_at 11 #v[gpow 6, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 12) = some (E.ofLimbs 1 0 0)
    rw [one_mul]; exact read_at 12 #v[1, 0, 0]

/-- `JumpSpec` on the taken row: the branch is taken, to `(g^6, 1)`. -/
theorem jump_spec : JumpSpec jumpRow ⟨gpow 6, 1⟩ tabData :=
  ⟨jump_bindings, by
    show step (programOf tabData) (imageOf tabData).2 ⟨gpow 4, 1⟩ = some ⟨gpow 6, 1⟩
    rw [step_of_fetch_eq_some (r := ⟨gpow 4, 1⟩)
      (fetch_at 4 (.jump (gpow 10) (gpow 11) (gpow 12)))]
    simp only [execute, one_mul, read_at 10 #v[1, 0, 0], read_at 11 #v[gpow 6, 0, 0],
      read_at 12 #v[1, 0, 0]]
    decide +kernel⟩

/-- `JumpSpec` on the untaken row: fall-through to `(g^9, 1)`. -/
theorem jump0_spec : JumpSpec jumpRow0 ⟨g * gpow 8, 1⟩ tabData :=
  ⟨jump0_bindings, by
    show step (programOf tabData) (imageOf tabData).2 ⟨gpow 8, 1⟩ = some ⟨g * gpow 8, 1⟩
    rw [step_of_fetch_eq_some (r := ⟨gpow 8, 1⟩)
      (fetch_at 8 (.jump (gpow 13) (gpow 11) (gpow 12)))]
    simp only [execute, one_mul, read_at 13 #v[0, 0, 0], read_at 11 #v[gpow 6, 0, 0],
      read_at 12 #v[1, 0, 0]]
    decide +kernel⟩

/-- Both rows are accepted by `main` in their honest environments, witnesses included. -/
example : ConstraintsHold.Completeness (jumpEnv tabData jumpRow)
    ((jumpTable.main (const jumpRow)).operations 0) :=
  jumpRow_complete ⟨_, jump_spec⟩

example : ConstraintsHold.Completeness (jumpEnv tabData jumpRow0)
    ((jumpTable.main (const jumpRow0)).operations 0) :=
  jumpRow_complete ⟨_, jump0_spec⟩

/-- `main` returns the pushed successors: `b = 1` selects `(d, f)`, `b = 0` the fall-through. -/
example : eval (jumpEnv tabData jumpRow).toEnvironment ((jumpTable.main (const jumpRow)).output 0) =
    ⟨gpow 6, 1⟩ := by
  rw [jump_output, ProvableType.eval_const]
  show (⟨_, _⟩ : Regs K) = ⟨gpow 6, 1⟩
  decide +kernel

example : eval (jumpEnv tabData jumpRow0).toEnvironment
    ((jumpTable.main (const jumpRow0)).output 0) = ⟨g * gpow 8, 1⟩ := by
  rw [jump_output, ProvableType.eval_const]
  show (⟨_, _⟩ : Regs K) = ⟨g * gpow 8, 1⟩
  decide +kernel

-- Clean's array generator computes the same two witnesses as `jumpEnv` holds: `w = 1⁻¹ = 1`,
-- `b = 1` on the taken row, `w = 0`, `b = 0` on the untaken one (compiled).
#guard (jumpTable.main (const jumpRow)).witgen default #[] = #[1, 1]
#guard (jumpTable.main (const jumpRow0)).witgen default #[] = #[0, 0]

example : (jumpEnv tabData jumpRow).get 0 = 1 ∧ (jumpEnv tabData jumpRow).get 1 = 1 := by
  decide +kernel

/-- The wrong witness `b = 1` at `v_cond = 0` fails the first residual `b + v_cond·w = 0` of
`main` for every inverse `w` (acceptance test 8): booleanity of `b` alone would have accepted
it. -/
example (get : ℕ → K) (hb : get 1 = 1) :
    ¬ ConstraintsHold.Soundness ⟨get, tabData⟩ ((jumpTable.main (const jumpRow0)).operations 0) := by
  intro h
  have hres := (jump_residuals_of_constraints h).1
  rw [ProvableType.eval_const] at hres
  dsimp only at hres
  have h1 : get 1 + (0 : K) * get 0 = 0 := hres
  rw [zero_mul, add_zero, hb] at h1
  exact one_ne_zero h1

/-- With `v_cond = 0` the residuals force `b = 0`, whatever `w`. -/
example (w b : K) (h1 : b + 0 * w = 0) (h2 : 0 * (b + 1) = 0) : b = 0 := by
  simpa using flags_sound h1 h2

/-! ## `BLAKE2S` -/

/-- The honest `BLAKE2S` row at `pc = g^5`: the executor's cells at `g^16 … g^24`. -/
def blake2sRow : Blake2sRow K :=
  ⟨gpow 5, 1, gpow 16, gpow 17, gpow 18, gpow 19, gpow 20, gpow 22, gpow 24,
    rustM0, rustM1, rustM2, rustM3, rustOut0, rustOut1, rustCv0, rustCv1, rustMd,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

/-- A canonical cell read at `1 · g^k` of a well-shaped thirty-two-word data. -/
theorem readCell {data : ProverData K} (hlog : (imageOf data).1 = 5) (hws : WellShapedData data)
    (k : ℕ) (c : Vector K 2) (hk : k < 32 := by decide)
    (hv : (memRows data)[k]'(by rw [hws.memRows_size, hlog]; exact hk) = cell c :=
      by decide +kernel) :
    (imageOf data).2.read (1 * gpow k) = some (cellOf c) := by
  rw [one_mul]; exact readAt hlog hws k (cell c) hk hv

/-- The nine cell reads of a row over a well-shaped data whose cells at `16..24` are the row's:
the binding, up to the fetched instruction. -/
theorem blake2s_reads {data : ProverData K} (hlog : (imageOf data).1 = 5)
    (hws : WellShapedData data) (r : Blake2sRow K)
    (hr : r = ⟨gpow 5, 1, gpow 16, gpow 17, gpow 18, gpow 19, gpow 20, gpow 22, gpow 24,
      r.m0, r.m1, r.m2, r.m3, r.out0, r.out1, r.cv0, r.cv1, r.md, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩)
    (hfetch : (programOf data).fetch (gpow 5) =
      some (.blake2s ![gpow 16, gpow 17, gpow 18, gpow 19] (gpow 20) (gpow 22) (gpow 24)))
    (h16 : (memRows data)[16]'(by rw [hws.memRows_size, hlog]; decide) = cell r.m0)
    (h17 : (memRows data)[17]'(by rw [hws.memRows_size, hlog]; decide) = cell r.m1)
    (h18 : (memRows data)[18]'(by rw [hws.memRows_size, hlog]; decide) = cell r.m2)
    (h19 : (memRows data)[19]'(by rw [hws.memRows_size, hlog]; decide) = cell r.m3)
    (h20 : (memRows data)[20]'(by rw [hws.memRows_size, hlog]; decide) = cell r.cv0)
    (h21 : (memRows data)[21]'(by rw [hws.memRows_size, hlog]; decide) = cell r.cv1)
    (h22 : (memRows data)[22]'(by rw [hws.memRows_size, hlog]; decide) = cell r.out0)
    (h23 : (memRows data)[23]'(by rw [hws.memRows_size, hlog]; decide) = cell r.out1)
    (h24 : (memRows data)[24]'(by rw [hws.memRows_size, hlog]; decide) = cell r.md) :
    Blake2sRowBindings r data := by
  rw [hr]
  refine ⟨hfetch, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact readCell hlog hws 16 r.m0 (by decide) h16
  · exact readCell hlog hws 17 r.m1 (by decide) h17
  · exact readCell hlog hws 18 r.m2 (by decide) h18
  · exact readCell hlog hws 19 r.m3 (by decide) h19
  · exact readCell hlog hws 20 r.cv0 (by decide) h20
  · show (imageOf data).2.read (1 * (g * gpow 20)) = some (cellOf r.cv1)
    rw [g_mul_gpow]; exact readCell hlog hws 21 r.cv1 (by decide) h21
  · exact readCell hlog hws 22 r.out0 (by decide) h22
  · show (imageOf data).2.read (1 * (g * gpow 22)) = some (cellOf r.out1)
    rw [g_mul_gpow]; exact readCell hlog hws 23 r.out1 (by decide) h23
  · exact readCell hlog hws 24 r.md (by decide) h24

theorem blake2s_bindings : Blake2sRowBindings blake2sRow tabData :=
  blake2s_reads (dataOf_logSize rfl) (dataOf_wellShaped rfl) blake2sRow rfl (fetch_at 5 _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The named assumption holds of the honest row: the executor's cells compress. -/
theorem blake2s_relation : Blake2sRelation blake2sRow := by
  show CompressCells _ _ _ _ _ _
  decide +kernel

/-- `Blake2sSpec` on the honest row, through `blake2s_spec_iff`: bound, compressing, and the
successor is `(g · g^5, 1)`. -/
theorem blake2s_spec : Blake2sSpec blake2sRow ⟨g * gpow 5, 1⟩ tabData :=
  (blake2s_spec_iff _ _ _).mpr ⟨blake2s_bindings, blake2s_relation, rfl⟩

/-- …and its step, decided in the kernel directly. -/
example : step (programOf tabData) (imageOf tabData).2 ⟨gpow 5, 1⟩ = some ⟨g * gpow 5, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 5, 1⟩)
    (fetch_at 5 (.blake2s ![gpow 16, gpow 17, gpow 18, gpow 19] (gpow 20) (gpow 22) (gpow 24)))]
  simp only [execute, one_mul, g_mul_gpow, Matrix.cons_val, Fin.isValue, read_at 16 (cell rustM0),
    read_at 17 (cell rustM1), read_at 18 (cell rustM2), read_at 19 (cell rustM3),
    read_at 20 (cell rustCv0), read_at 21 (cell rustCv1), read_at 22 (cell rustOut0),
    read_at 23 (cell rustOut1), read_at 24 (cell rustMd), Option.bind_eq_bind, Option.bind_some]
  decide +kernel

example : ConstraintsHold.Completeness (rowEnv tabData)
    ((blake2sTable.main (const blake2sRow)).operations 0) :=
  blake2sRow_complete_of_spec ⟨_, blake2s_spec⟩

example : eval (rowEnv tabData).toEnvironment ((blake2sTable.main (const blake2sRow)).output 0) =
    ⟨g * gpow 5, 1⟩ := by
  simp only [blake2s_output, ProvableType.eval_const, blake2sRow]

/-- A non-canonical cell is rejected (acceptance test 12): an image whose second output cell has
a nonzero top limb does not balance the row's canonical read of it, so the constraints `main`
emits on the honest row fail in every environment over that image. -/
def badMem : Array (Vector K 3) := memTable.set! 23 #v[rustOut1[0], rustOut1[1], 1]

example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, dataOf badMem⟩
      ((blake2sTable.main (const blake2sRow)).operations 0) := by
  intro h
  have hb := blake2s_bindings_of_constraints
    (by rw [ProvableType.eval_const]; exact blake2s_relation) h
  rw [ProvableType.eval_const] at hb
  dsimp only at hb
  obtain ⟨-, -, -, -, -, -, -, -, hout1, -⟩ := hb
  rw [show blake2sRow.fp * (g * blake2sRow.oout) = 1 * (g * gpow 22) from rfl, one_mul,
    g_mul_gpow, readAt (dataOf_logSize (mem := badMem) rfl) (dataOf_wellShaped rfl) 23
      #v[rustOut1[0], rustOut1[1], 1]] at hout1
  exact absurd (Option.some.inj hout1) (by decide +kernel)

/-- The boundary with Flock: an output cell holding a wrong but canonical word, consistently in
the row and in the image. The row is bound and locally complete, and it fails the compression
relation and the functional specification: that failure is Flock's to enforce. -/
def wrongOut1 : Vector K 2 := #v[rustOut1[0], rustOut1[1] + 1]

def wrongMem : Array (Vector K 3) := memTable.set! 23 (cell wrongOut1)

def blake2sRow' : Blake2sRow K := { blake2sRow with out1 := wrongOut1 }

theorem blake2s'_bindings : Blake2sRowBindings blake2sRow' (dataOf wrongMem) :=
  blake2s_reads (dataOf_logSize (mem := wrongMem) rfl) (dataOf_wellShaped rfl) blake2sRow' rfl
    (fetchAt wrongMem rfl 5 _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : ConstraintsHold.Completeness (rowEnv (dataOf wrongMem))
    ((blake2sTable.main (const blake2sRow')).operations 0) :=
  blake2sRow_complete blake2s'_bindings

theorem blake2s'_no_relation : ¬ Blake2sRelation blake2sRow' := by
  show ¬ CompressCells _ _ _ _ _ _
  decide +kernel

example (next : Regs K) : ¬ Blake2sSpec blake2sRow' next (dataOf wrongMem) := fun h ↦
  blake2s'_no_relation ((blake2s_spec_iff _ _ _).mp h).2.1

end LeanerVMTests.Arithmetization.Tables
