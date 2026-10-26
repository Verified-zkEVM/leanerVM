module

public import Statement.Extractor

/-!
# The witness of an execution, executable

The executable honest prover's first piece: from a trace, one forward run through the address
indices (`powIndex`, `gLogIn` of `Extractor.lean`), then the six opcode tables' rows with their
read counts, the memory's and the bytecode's finalize counts kept as arrays by index.

* `stepsFrom`, `runSteps`: the run, `step` computed through the two indices (`stepIn`), recording
  each state stepped from, its bytecode slot and the instruction fetched there; `none` if a step
  fails, the machine halts early, or it is not in the final state after `t.steps` steps.
* `checkTrace`: the execution is valid (`ValidExecution`) and its committed size is at most
  `2^28` (`Trace.committedSize`), decided by that one run; `opCount` the instruction counts
  (`Trace.count`).
* `rowsOf`: the rows of the run, table by table, each read carrying the count of its cell so far
  (`g^n` for the `n`-th read of the cell), the counters stepping by `g` in place, and the
  bytecode slot's count likewise: the raw rows of `rowOf` (lean_vm,
  `Arithmetization/Completeness/Rows.lean`), written out as arrays (`rowIn`).

The columns, the sizes and the stack of these rows are in `Statement/Prover/Columns.lean`. What
each definition computes is proved in `lean_vm/LeanVM/Prover/Witness*.lean`.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol.Verifier

/-! ## The run -/

/-- One step of a run: the state stepped from, the bytecode slot of its counter, and the
instruction fetched there. -/
structure Step where
  /-- The program counter stepped from. -/
  pc : K
  /-- The frame pointer stepped from. -/
  fp : K
  /-- The bytecode slot of `pc`: `pc = g^slot`. -/
  slot : ℕ
  /-- The instruction fetched at `pc`. -/
  ins : Instr

/-- The memory reader through the index `memIdx` (`MemImage.read`, computed). -/
def readIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemImage κ) (a : K) : Option E :=
  (gLogIn memIdx κ a).map img

/-- `n` steps from `r` (`run`, computed through the indices, the instruction of slot `i` read
from `code`, `prog.code` tabulated), the steps taken pushed on `acc`: the steps and the state
reached; `none` if a step fails or the machine halts first. -/
def stepsFrom (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : Program)
    (code : Vector Instr (2 ^ prog.logSize)) {κ : ℕ} (img : MemImage κ) :
    ℕ → Regs K → Array Step → Option (Array Step × Regs K)
  | 0, r, acc => some (acc, r)
  | n + 1, r, acc =>
    if r = Regs.final prog then none
    else
      match gLogIn codeIdx prog.logSize r.pc with
      | none => none
      | some i =>
        match executeWith (readIn memIdx img) r code[i] with
        | none => none
        | some r' =>
          stepsFrom memIdx codeIdx prog code img n r' (acc.push ⟨r.pc, r.fp, i.val, code[i]⟩)

/-- **The run of a trace**: its `t.steps` steps from the initial state, when they end in the
final state; `none` otherwise. The program's instructions are tabulated once. -/
def runSteps (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : Program) (t : Trace prog) :
    Option (Array Step) :=
  match stepsFrom memIdx codeIdx prog (Vector.ofFn prog.code) t.image t.steps Regs.initial
    #[] with
  | some (acc, r) => if r = Regs.final prog then some acc else none
  | none => none

/-- The number of steps of opcode `op` (`Trace.count`, computed). -/
def opCount (steps : Array Step) (op : Opcode) : ℕ :=
  steps.countP fun st ↦ decide (st.ins.opcode = op)

/-- The committed size of an execution from its memory log-size and its counts
(`Trace.committedSize`, with `log2Ceil` for `Nat.clog 2`). -/
def committedSizeOf (logSize κ : ℕ) (count : Opcode → ℕ) : ℕ :=
  let height (op : Opcode) : ℕ := 2 ^ log2Ceil (count op)
  let keccakHeight : ℕ := 2 ^ max (log2Ceil (count .keccak)) 9
  4 * 2 ^ κ + 2 ^ logSize +
    15 * height .xor + 15 * height .mulNative + 8 * height .setConstant + 15 * height .deref +
    14 * height .jump + 26 * keccakHeight + 2 ^ 6 * keccakHeight

/-- The greatest committed size the verifier admits, `2^28` (`MAX_MU`, `pcs.rs:51`). -/
def maxCommitted : ℕ := 2 ^ 28

/-- **The check of a trace**: it has the public boundary of `input`, its run ends in the final
state, and its committed size is at most `2^28`; one run through the address indices. -/
def checkTrace (prog : Program) (input : PublicInput) (t : Trace prog) : Bool :=
  boundaryOK input t &&
    match runSteps (powIndex t.κ) (powIndex prog.logSize) prog t with
    | some steps => decide (committedSizeOf prog.logSize t.κ (opCount steps) ≤ maxCommitted)
    | none => false

/-! ## The rows -/

/-- The limbs of the word at `a`, zero when there is none (`MemImage.limbsAt`, computed). -/
def limbsIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemImage κ) (a : K) : Vector K 3 :=
  match readIn memIdx img a with
  | some v => #v[v.limb 0, v.limb 1, v.limb 2]
  | none => #v[0, 0, 0]

/-- The cells an instruction reads, in the order its row's reads carry them (`readAddrs`,
computed). -/
def addrsIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemImage κ) (fp : K) :
    Instr → List K
  | .xor oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .mulNative oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .setConstant o _ => [fp * o]
  | .deref o1 o2 o3 _ => [fp * o1, (limbsIn memIdx img (fp * o1))[0] * o2, fp * o3]
  | .jump oc od of => [fp * oc, fp * od, fp * of]
  | .keccak om otail ob8 ocap oout _ _ =>
      [fp * om 0,
        fp * om 1,
        fp * om 2,
        fp * om 3,
        fp * (g ^ 0 * otail),
        fp * (g ^ 1 * otail),
        fp * (g ^ 2 * otail),
        fp * (g ^ 3 * otail),
        fp * ob8,
        fp * (g ^ 0 * ocap),
        fp * (g ^ 1 * ocap),
        fp * (g ^ 2 * ocap),
        fp * (g ^ 3 * ocap),
        fp * (g ^ 0 * oout),
        fp * (g ^ 1 * oout),
        fp * (g ^ 2 * oout),
        fp * (g ^ 3 * oout),
        fp * (g ^ 4 * oout),
        fp * (g ^ 5 * oout),
        fp * (g ^ 6 * oout),
        fp * (g ^ 7 * oout),
        fp * (g ^ 8 * oout),
        fp * (g ^ 9 * oout),
        fp * (g ^ 10 * oout),
        fp * (g ^ 11 * oout),
        fp * (g ^ 12 * oout)]

/-- The counts of a sequence of reads: each read gets its cell's counter, which then steps by
`g`, in place; the counts are pushed on `cs`. -/
def countReads (memIdx : Std.HashMap UInt64 ℕ) (κ : ℕ) :
    List K → Array K → Array K → Array K × Array K
  | [], cs, ctr => (cs, ctr)
  | a :: rest, cs, ctr =>
    match gLogIn memIdx κ a with
    | some i => countReads memIdx κ rest (cs.push (ctr.getD i.val 1)) (ctr.modify i.val (g * ·))
    | none => countReads memIdx κ rest (cs.push 1) ctr

/-- The cells a `KECCAK` with these operands reads at `fp`, the zero word where a read fails
(`keccakInputCells`, computed). -/
def keccakInputIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemImage κ) (fp : K)
    (om : Fin 4 → K) (otail ob8 ocap : K) (c : Fin 13) : E :=
  (readIn memIdx img (fp * keccakInOffset om otail ob8 ocap c)).getD 0

/-- The lane `l` of a state, as a `K` word. -/
def laneK (S : KState) (l : ℕ) : K := K.ofLane (Keccak.lane S l)

/-- The raw row of an instruction executed from `(pc, fp)` (`rowOf`, computed): the typed row of
its table as an array, with the read counts `c 0, c 1, …` and the bytecode count `rbc`. -/
def rowIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemImage κ) (pc fp : K) (c : ℕ → K)
    (rbc : K) : Instr → Array K
  | .xor oA oB oC =>
    let vA := limbsIn memIdx img (fp * oA)
    let vB := limbsIn memIdx img (fp * oB)
    #[pc, fp, oA, oB, oC, vA[0], vA[1], vA[2], vB[0], vB[1], vB[2], c 0, c 1, c 2, rbc]
  | .mulNative oA oB oC =>
    let vA := limbsIn memIdx img (fp * oA)
    let vB := limbsIn memIdx img (fp * oB)
    #[pc, fp, oA, oB, oC, vA[0], vA[1], vA[2], vB[0], vB[1], vB[2], c 0, c 1, c 2, rbc]
  | .setConstant o k => #[pc, fp, o, k.limb 0, k.limb 1, k.limb 2, c 0, rbc]
  | .deref o1 o2 o3 mode =>
    let v3 := limbsIn memIdx img (fp * o3)
    #[pc, fp, o1, o2, o3, (derefFlags mode).1, (derefFlags mode).2,
      (limbsIn memIdx img (fp * o1))[0], v3[0], v3[1], v3[2], c 0, c 1, c 2, rbc]
  | .jump oc od of =>
    let vc := (limbsIn memIdx img (fp * oc))[0]
    #[pc, fp, oc, od, of, vc, (limbsIn memIdx img (fp * od))[0],
      (limbsIn memIdx img (fp * of))[0], c 0, c 1, c 2, rbc,
      if vc = 0 then 0 else vc⁻¹, if vc = 0 then 0 else 1]
  | .keccak om otail ob8 ocap oout inOdd outOdd =>
    let input := keccakInputIn memIdx img fp om otail ob8 ocap
    let S := stateOfCells input inOdd
    let out := keccakF S
    #[pc, fp, om 0, om 1, om 2, om 3, otail, ob8, ocap, oout, flagK inOdd, flagK outOdd,
        if inOdd then (input 0).limb 0 else (input 8).limb 1] ++
      Array.ofFn (fun l : Fin 25 ↦ laneK S l) ++ Array.ofFn (fun l : Fin 25 ↦ laneK out l) ++
      Array.ofFn (fun j : Fin 26 ↦ c j) ++ #[rbc]

/-- The table of an opcode, in the ensemble's order. -/
def opTableIdx : Opcode → ℕ
  | .xor => 0
  | .mulNative => 1
  | .setConstant => 2
  | .deref => 3
  | .jump => 4
  | .keccak => 5

/-- The rows built so far: the six tables' rows, the memory cells' and the bytecode slots'
counters (`g^n` after `n` reads). -/
structure Rows where
  /-- The six opcode tables' rows, in the ensemble's order. -/
  tabs : Array (Array (Array K))
  /-- The memory cells' counters, by index. -/
  mem : Array K
  /-- The bytecode slots' counters, by index. -/
  bc : Array K

/-- The rows of one more step: its reads take their cells' counts, its bytecode read its slot's,
and its row is pushed on its table. -/
def stepRows (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemImage κ) (acc : Rows)
    (st : Step) : Rows :=
  -- the fields taken out first, so that each counter array is updated in place
  let ⟨tabs, mem, bc⟩ := acc
  let (cs, mem) := countReads memIdx κ (addrsIn memIdx img st.fp st.ins) #[] mem
  let row := rowIn memIdx img st.pc st.fp (fun j ↦ cs.getD j 1) (bc.getD st.slot 1) st.ins
  ⟨tabs.modify (opTableIdx st.ins.opcode) (·.push row), mem, bc.modify st.slot (g * ·)⟩

/-- **The rows of a run**: one pass over its steps, from empty tables and every counter `1`. -/
def rowsOf (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemImage κ) (logSize : ℕ)
    (steps : Array Step) : Rows :=
  steps.foldl (stepRows memIdx img)
    ⟨Array.replicate 6 #[], Array.replicate (2 ^ κ) 1, Array.replicate (2 ^ logSize) 1⟩

end LeanVM.Prover

end
