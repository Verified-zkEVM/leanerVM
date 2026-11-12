/-
  LeanerVMWitgen

  Executions of compiled leanVM programs by the pinned Rust executor, read natively into
  `Program`, `PublicInput` and `Trace prog` and checked against the reference semantics, timed;
  the end-to-end harness of a witness generator.
-/

import LeanerVM.Protocol.Prove
import LeanerVM.Protocol.Verify
import LeanerVM.Semantics.TraceInput
import LeanerVM.Semantics.FillBlocks
import LeanerVM.Arithmetization.WitnessGen
import LeanerVM.Arithmetization.HypothesisChecks
import LeanerVM.Protocol.Headline

/-!
# The `leanervm-witgen` executable

`leanervm-witgen [--prod] [--hash] [--gen] [--prove] [--stages] file…` reads each file written by
`scripts/dump-execution-rust.sh` (an execution of a compiled program by the Rust executor at
leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`, plain or `gzip`ped) and checks, each step
timed:

* the reading: the typed program (`Program`), the public input (`PublicInput`), the trace
  (`Trace prog`, through `TraceInput.adapt` from the image and the Rust counts), whose log-size and
  step count must be the file's;
* `SentinelSafe prog`, decided, and the fill blocks the Rust lists: each of the 48 pairs of table
  and size has a listed block whose slots hold the dummies and the closing jump (`IsFillBlock` at
  that start; a diagnostic of the listed starts, not a decision procedure for `HasFillBlocks`);
* `WellFormedBytecode prog`, decided by `wellFormedB` (`wellFormedB_eq_true_iff`);
* with `--hash`, `programHash prog` against the Rust bytecode digest;
* the execution: `checkTrace` (`checkTrace_eq_true_iff`, so it decides `ValidExecution`), whose
  run reads through a table of powers grown along the run;
* `t.Fits`, decided by `fitsBy` from the rows of the run counted by a forward pass
  (`fitsBy_eq_true_iff`, on a valid execution);
* `StackFits prog t`, decided by `stackFitsRowsB` on the same counts (`stackFitsRowsB_eq_true_iff`);
* the rows: the main run's states, replayed, are each table's first `main` rows in order, and the
  remaining rows of every table, the fill rows, step to a permutation of themselves away from the
  sentinel (`FillerRowsValid`, checked by sorting; a diagnostic, not proved equal to
  `checkFillerRows`);
* with `--prod`, `checkTrace` again, its table seeded with the Rust hint list (the cells some row
  accessed and the row counters).

With `--gen`, `runGenerator` runs `witnessGen` (a function of the shape `Generator`) and reports
the witness's sizes, whose table heights must be the Rust's unless the Rust prover raised them to a
floor on the committed size; with `--prove`, it also proves the witness (`prove`, rate `1/2`) and
checks the proof with `verify`; each timed. With `--stages`, the stages of `witnessGen` are forced
and timed one by one (`stages`). The exit code is `1` if a check fails, and `2`, with a usage
line, when no file is given.
-/

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol
open LeanerVM.Protocol.Verify

namespace LeanerVMWitgen

/-! ## The powers of `g` -/

/-- The power `g ^ i`, from the table. -/
def powAt (P : PowTable) (i : ℕ) : K := P.pow i

/-- One step through a table of powers. -/
def stepWith {κ : ℕ} (prog : Program) (image : MemImage κ) (P : PowTable) (r : Regs K) :
    Option (Regs K) :=
  fetchBy prog P r.pc >>= executeWith (readBy image P) r

/-! ## The file -/

/-- What a file of `scripts/dump-execution-rust.sh` holds. -/
structure Execution where
  /-- The Rust revision the file names. -/
  pin : String
  /-- The program's name. -/
  name : String
  /-- The program. -/
  prog : Program
  /-- The Rust bytecode digest. -/
  programHash : Digest
  /-- The fill blocks the compiler placed: start, size, table. -/
  filler : Array (ℕ × ℕ × ℕ)
  /-- The public input. -/
  input : PublicInput
  /-- The memory log-size. -/
  κ : ℕ
  /-- Main-run transitions to the sentinel. -/
  steps : ℕ
  /-- The bytes of memory the Rust used before padding. -/
  memUsed : ℕ
  /-- The number of cells read and never written. -/
  unconstrainedReads : ℕ
  /-- The Rust prover's floor on the committed size, `0` for none. -/
  floor : ℕ
  /-- The final image and the Rust counts. -/
  traceInput : TraceInput
  /-- The cells some row accessed. -/
  accessed : Array ℕ
  /-- The rows of the six tables, `(pc, fp)` as exponents, in row order. -/
  rows : Vector (Array (ℕ × ℕ)) 6

/-- The parser: the lines and the next line's index. -/
abbrev ParseM := StateT ℕ (ReaderT (Array String) (Except String))

/-- The next line's words. -/
def words : ParseM (List String) := do
  let ls ← read
  let i ← get
  if h : i < ls.size then
    set (i + 1)
    return (ls[i].splitOn " ").filter (· ≠ "")
  else throw "unexpected end of file"

/-- A numeral. -/
def num (s : String) : ParseM ℕ :=
  match s.toNat? with
  | some n => pure n
  | none => do throw s!"line {← get}: not a numeral: {s}"

/-- A hexadecimal word of `K`. -/
def hexK (s : String) : ParseM K := do
  let digit (c : Char) : Option ℕ :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  match s.foldl (fun acc c ↦ acc.bind fun n ↦ (digit c).map (16 * n + ·)) (some 0) with
  | some n => if n < 2 ^ 64 then pure (K.ofBits n) else throw s!"word too large: {s}"
  | none => throw s!"not hexadecimal: {s}"

/-- A line `key v…`, its values. -/
def keyed (k : String) : ParseM (List String) := do
  match ← words with
  | k' :: vs => if k' == k then pure vs else throw s!"line {← get}: expected {k}, read {k'}"
  | [] => throw s!"line {← get}: expected {k}"

/-- A line `key n`, its number. -/
def keyedNum (k : String) : ParseM ℕ := do
  match ← keyed k with
  | [n] => num n
  | _ => throw s!"line {← get}: {k} takes one number"

/-- One instruction line (`scripts/dump-proof-rust.sh`), operands `g ^ j` from the table. -/
def instrOf (pows : PowTable) : List String → ParseM Instr
  | ["xor", a, b, c] => do return .xor (← o a) (← o b) (← o c)
  | ["mul", a, b, c] => do return .mulNative (← o a) (← o b) (← o c)
  | ["set", a, k0, k1, k2] => do
    return .setConstant (← o a) (E.ofLimbs (← hexK k0) (← hexK k1) (← hexK k2))
  | ["deref", a, b, c, m] => do
    let mode ← match m with
      | "cell" => pure DerefMode.cell
      | "pc" => pure .pc
      | "fp" => pure .fp
      | _ => throw s!"bad mode {m}"
    return .deref (← o a) (← o b) (← o c) mode
  | ["jump", c, d, f] => do return .jump (← o c) (← o d) (← o f)
  | ["blake2s", i0, i1, i2, i3, cv, out, md] => do
    let m0 ← o i0
    let m1 ← o i1
    let m2 ← o i2
    let m3 ← o i3
    return .blake2s ![m0, m1, m2, m3] (← o cv) (← o out) (← o md)
  | ws => do throw s!"line {← get}: not an instruction: {ws}"
where
  o (s : String) : ParseM K := do return powAt pows (← num s)

/-- A digest from 64 hexadecimal digits, as `RustProof.hexDigest` reads it. -/
def digestOf (s : String) : ParseM Digest := do
  let cs := s.toList
  unless cs.length = 64 do throw "a digest has 64 digits"
  let bytes ← (List.range 32).mapM fun i ↦ do
    let k ← hexK (String.ofList [cs.getD (2 * i) '0', cs.getD (2 * i + 1) '0'])
    return k.toBitVec.toNat.toUInt8
  return Blake2sHash.digestOfBytes bytes

/-- `n` lines read by `f`. -/
def many {α : Type} (n : ℕ) (f : List String → ParseM α) : ParseM (Array α) := do
  let mut a := Array.mkEmpty n
  for _ in [0:n] do
    a := a.push (← f (← words))
  return a

/-- Read a file; `pows` must hold the powers the operands name. -/
def parse (pows : PowTable) : ParseM Execution := do
  let (pin, name) ← match ← keyed "leanisa-execution" with
    | [p, n] => pure (p, n)
    | _ => throw "bad header"
  let n ← keyedNum "program"
  let ops ← many n (instrOf pows)
  let k := Nat.log 2 n
  let prog ← if h : k ≤ maxLogBytecode ∧ 2 ^ k = n then
      pure (⟨k, h.1, fun i ↦ ops.getD i.val (.xor 0 0 0)⟩ : Program)
    else throw "the program size is not a power of two within the cap"
  let hash ← match ← keyed "program_hash" with
    | [h] => digestOf h
    | _ => throw "bad program_hash"
  let filler ← many (← keyedNum "filler") fun
    | [p, s, t] => do return (← num p, ← num s, ← num t)
    | _ => throw "bad fill block"
  let input ← match ← keyed "public" with
    | [a0, a1, a2, b0, b1, b2] => do
      unless a2.all (· == '0') && b2.all (· == '0') do throw "a public word has a third limb"
      pure (⟨![← hexK a0, ← hexK a1, ← hexK b0, ← hexK b1]⟩ : PublicInput)
    | _ => throw "bad public"
  let κ ← keyedNum "kappa"
  let steps ← keyedNum "steps"
  let cycles ← keyedNum "cycles"
  let memUsed ← keyedNum "mem_used"
  let unconstrained ← keyedNum "unconstrained_reads"
  let floor ← keyedNum "min_log_committed"
  let six (k : String) : ParseM (Vector ℕ 6) := do
    let vs ← (← keyed k).mapM num
    if h : vs.length = 6 then return ⟨vs.toArray, h⟩ else throw s!"{k} takes six counts"
  let mainCounts ← six "main"
  let rowCounts ← six "rows"
  let cells ← many (← keyedNum "memory") fun
    | [i, c0, c1, c2] => do return (← num i, E.ofLimbs (← hexK c0) (← hexK c1) (← hexK c2))
    | _ => throw "bad memory line"
  if 2 ^ κ ≤ cells.foldl (fun m c ↦ max m (c.1 + 1)) 0 ∨ κ > 40 then throw "a cell beyond 2^κ"
  let memory := cells.foldl (fun a c ↦ a.set! c.1 c.2) (Array.replicate (2 ^ κ) 0)
  let accessed ← many (← keyedNum "accessed") fun
    | [i] => num i
    | _ => throw "bad accessed line"
  let mut rows : Array (Array (ℕ × ℕ)) := #[]
  for t in [0:6] do
    match ← keyed "table" with
    | [t', m] =>
      unless (← num t') = t do throw "tables out of order"
      rows := rows.push (← many (← num m) fun
        | [pc, fp] => do return (← num pc, ← num fp)
        | _ => throw "bad row")
    | _ => throw "bad table line"
  let _ ← keyed "end"
  let tables ← if h : rows.size = 6 then pure (⟨rows, h⟩ : Vector _ 6) else throw "six tables"
  return {
    pin := pin, name := name, prog := prog, programHash := hash, filler := filler,
    input := input, κ := κ, steps := steps, memUsed := memUsed,
    unconstrainedReads := unconstrained, floor := floor,
    traceInput := ⟨memory, mainCounts, rowCounts, cycles⟩, accessed := accessed, rows := tables }

/-- The largest exponent a file names: its program and its memory's sizes. -/
def sizesOf (lines : Array String) : ℕ × ℕ := Id.run do
  let mut b := 0
  let mut κ := 0
  for l in lines do
    match (l.splitOn " ") with
    | ["program", n] => b := n.toNat?.getD 0
    | ["kappa", k] => κ := k.toNat?.getD 0
    | _ => pure ()
    if κ ≠ 0 then break
  return (b, κ)

/-! ## The checks -/

/-- The table of an opcode, in the Rust's order XOR, MUL, SET, DEREF, JUMP, BLAKE2S. -/
def tableOf : Opcode → Fin 6
  | .xor => 0
  | .mulNative => 1
  | .setConstant => 2
  | .deref => 3
  | .jump => 4
  | .blake2s => 5

/-- The opcodes in table order. -/
def opcodes : List Opcode := [.xor, .mulNative, .setConstant, .deref, .jump, .blake2s]

/-- The listed fill blocks hold the dummies and the closing jump, and every pair of table and
size has one. -/
def fillBlocksListed (prog : Program) (filler : Array (ℕ × ℕ × ℕ)) : Bool :=
  let code (i : ℕ) : Option Instr :=
    if h : i < 2 ^ prog.logSize then some (prog.code ⟨i, h⟩) else none
  let blockOk : ℕ × ℕ × ℕ → Bool := fun (p, s, t) ↦
    match opcodes[t]? with
    | none => false
    | some op => decide (p + s + 1 < 2 ^ prog.logSize) &&
        (List.range s).all (fun i ↦ code (p + i) == some (fillDummy op)) &&
        code (p + s) == some fillClose
  filler.all blockOk && opcodes.all fun op ↦ fillSizes.all fun s ↦
    filler.any fun (_, s', t) ↦ s' == s && opcodes[t]? == some op

/-- The main run replayed through a table of powers: each table's states in order; `none` on a
failed step. -/
def mainRows {κ : ℕ} (prog : Program) (image : MemImage κ) (P : PowTable) (n : ℕ) :
    Option (Vector (Array (Regs K)) 6) := Id.run do
  let mut acc : Vector (Array (Regs K)) 6 := Vector.replicate 6 #[]
  let mut r := Regs.initial
  for _ in [0:n] do
    let some ins := fetchBy prog P r.pc | return none
    let i := tableOf ins.opcode
    acc := acc.set i (acc[i].push r)
    let some next := executeWith (readBy image P) r ins | return none
    r := next
  return some acc

/-- Two states as a sort key. -/
def regsKey (r : Regs K) : UInt64 × UInt64 := (wordKey r.pc, wordKey r.fp)

/-- Lexicographic order on keys. -/
def keyLt (a b : UInt64 × UInt64) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- The fill rows: away from the sentinel, each steps, and the successors are a permutation of
the starts (compared sorted). -/
def fillRowsOk {κ : ℕ} (prog : Program) (image : MemImage κ) (P : PowTable)
    (starts : Array (Regs K)) : Bool := Id.run do
  let mut next : Array (UInt64 × UInt64) := Array.mkEmpty starts.size
  for r in starts do
    if r.pc = prog.finalPc then return false
    let some s := stepWith prog image P r | return false
    next := next.push (regsKey s)
  return (starts.map regsKey).qsort keyLt == next.qsort keyLt

/-! ## The generator hook -/

/-- The shape of a witness generator: from an execution, a witness of the constraint statement at
memory log-size `κ + 1`. -/
abbrev Generator : Type 1 :=
  (prog : Program) → (input : PublicInput) → (t : Trace prog) →
    Option (Air.Flat.EnsembleWitness (leanIsaEnsemble prog (t.κ + 1)))

/-- Return a value through an opaque call, so that its computation stays inside a timed
interval. -/
@[noinline] def force {α : Type} (x : α) : IO α := pure x

/-- Seconds since `t0`. -/
def since (t0 : ℕ) : IO Float := do return ((← IO.monoNanosNow) - t0).toFloat / 1e9

/-- Generate a witness and report its sizes; with `proveToo`, prove at rate `ρ` with `fuel`
nonces a grind and verify; each timed. -/
def runGenerator (gen : Generator) (proveToo : Bool) (fuel ρ : ℕ) (prog : Program)
    (input : PublicInput) (t : Trace prog) (rustRows : Option (Vector ℕ 6)) : IO Bool := do
  let t0 ← IO.monoNanosNow
  match gen prog input t with
  | none =>
    IO.println s!"FAIL the generator returned none, in {← since t0} s"
    return false
  | some w =>
  let sizes ← force (LeanIsa.Sizes.ofWitness w)
  let some s := sizes | do
    IO.println s!"FAIL the witness has no sizes, in {← since t0} s"
    return false
  let same := rustRows.all fun rs ↦ (List.finRange 6).all fun j ↦ 2 ^ s.τ j == rs[j]
  let versus := match rustRows with
    | some rs => s!"the Rust's heights {rs.toList}: {if same then "equal" else "differ"}"
    | none => "the Rust's heights are floored, not compared"
  IO.println s!"{if same then "ok  " else "FAIL"} witnessGen: memory 2^{s.logMem}, tables \
    2^{List.ofFn s.τ} ({versus}), in {← since t0} s"
  unless same do return false
  unless proveToo do return true
  let t1 ← IO.monoNanosNow
  let some p ← force (prove fuel prog input w ρ) | do
    IO.println s!"FAIL prove returned none, in {← since t1} s"
    return false
  IO.println s!"  prove: {p.stream.length} scalars, in {← since t1} s"
  let t2 ← IO.monoNanosNow
  let ok ← force (verify prog input p)
  IO.println s!"{if ok then "ok  " else "FAIL"} verify = {ok}, in {← since t2} s"
  return ok

/-- The stages of `witnessGen`, each forced and timed (`--stages`). -/
def stages (prog : Program) (input : PublicInput) (t : Trace prog) : IO Unit := do
  let mut t0 ← IO.monoNanosNow
  let lap (name : String) (t0 : ℕ) : IO ℕ := do
    IO.println s!"  stage {name}: {← since t0} s"
    IO.monoNanosNow
  let tab ← force (fillStartTable prog)
  t0 ← lap "fillStartTable" t0
  let pcs := startsOf tab
  let P ← force (powTable (2 ^ max (t.κ + 1) prog.logSize))
  t0 ← lap s!"powTable ({P.pows.size})" t0
  let runA ← force (runSkelsBy (fetchBy prog P) (executeWith (readBy t.image P)) t.steps
    Regs.initial #[])
  t0 ← lap s!"runSkelsBy ({runA.size})" t0
  let runS ← force runA.toList
  let tabc ← force (skelCountTable runS)
  t0 ← lap "skelCountTable" t0
  let rows := countsOf tabc
  let some τ := jumpHeight (jumpOwed rows) | IO.println "no τ"
  let pad ← force (padSkels t.κ pcs (planCount rows τ))
  t0 ← lap s!"padSkels ({pad.length})" t0
  let S ← force (runS ++ pad)
  let img := padImage t.image pcs
  let rd := readBy img P
  let res ← force (mkRowsH rd ∅ ∅ S #[])
  t0 ← lap s!"mkRowsH ({res.1.size})" t0
  let R ← force res.1.toList
  for op in opcodes do
    let rs ← force (opRowsBy P rd R op)
    t0 ← lap s!"opRowsBy {tableOf op} ({rs.length})" t0
  let bc ← force (bcRowsBy P prog res.2.2.get)
  t0 ← lap s!"bcRowsBy ({bc.length})" t0
  let memP ← force (memRowsBy P img res.2.1.get)
  t0 ← lap s!"memRowsBy ({memP.length})" t0
  let w ← force ((witnessGen prog input t).map fun w ↦ (LeanIsa.Sizes.ofWitness w).isSome)
  discard <| lap s!"witnessGen ({w})" t0

/-! ## The run -/

/-- The options of a run. -/
structure Options where
  /-- Run `checkTrace` with the Rust hint list. -/
  prod : Bool := false
  /-- Check the program hash. -/
  hash : Bool := false
  /-- Run the witness generator. -/
  gen : Bool := false
  /-- Also prove and verify. -/
  prove : Bool := false
  /-- Time the generator's stages. -/
  stages : Bool := false

/-- Print a check's outcome and time; `1` if it failed. -/
def report (name : String) (ok : Bool) (t0 : ℕ) : IO ℕ := do
  IO.println s!"{if ok then "ok  " else "FAIL"} {name}: {← since t0} s"
  (← IO.getStdout).flush
  return if ok then 0 else 1

/-- The file's text, through `gzip -dc` for a `.gz` file. -/
def readText (file : String) : IO String := do
  if file.endsWith ".gz" then
    let out ← IO.Process.output { cmd := "gzip", args := #["-dc", file] }
    unless out.exitCode = 0 do throw (IO.userError s!"gzip failed on {file}")
    return out.stdout
  else IO.FS.readFile file

/-- Check one file; the number of failed checks. -/
def runFile (opts : Options) (gen : Generator) (file : String) : IO ℕ := do
  IO.println s!"== {file}"
  let t0 ← IO.monoNanosNow
  let text ← readText file
  let lines := (text.splitOn "\n").toArray
  let (b, κ) := sizesOf lines
  let pows ← force (powTable (max b (2 ^ min κ 40)))
  IO.println s!"  read {text.length} bytes, powers of g to 2^{Nat.log 2 pows.pows.size}: \
    {← since t0} s"
  let t1 ← IO.monoNanosNow
  let e ← match (parse pows).run 0 |>.run lines with
    | .ok (e, _) => pure e
    | .error msg => do IO.println s!"FAIL parse: {msg}"; return 1
  IO.println s!"  {e.name} (leanVM {e.pin.take 8}): program 2^{e.prog.logSize}, memory 2^{e.κ}, \
    steps {e.steps}, cycles {e.traceInput.cycles}, main {e.traceInput.mainCounts.toList}, \
    rows {e.traceInput.rowCounts.toList}, unconstrained reads {e.unconstrainedReads}, \
    committed floor 2^{e.floor}"
  let mut failed ← report "parse" true t1
  let t2 ← IO.monoNanosNow
  let some t := e.traceInput.adapt e.prog | do
    failed := failed + (← report "TraceInput.adapt" false t2)
    return failed
  failed := failed + (← report s!"TraceInput.adapt: κ = {t.κ}, steps = {t.steps}"
    (t.κ == e.κ && t.steps == e.steps) t2)
  let t3 ← IO.monoNanosNow
  failed := failed + (← report "SentinelSafe" (decide (SentinelSafe e.prog)) t3)
  let t4 ← IO.monoNanosNow
  failed := failed + (← report s!"fill blocks ({e.filler.size} listed)"
    (fillBlocksListed e.prog e.filler) t4)
  let t4w ← IO.monoNanosNow
  failed := failed + (← report "wellFormedB (= WellFormedBytecode)" (← force (wellFormedB e.prog))
    t4w)
  if opts.hash then
    let t5 ← IO.monoNanosNow
    failed := failed + (← report "programHash = the Rust bytecode digest"
      (programHash e.prog == e.programHash) t5)
  let t6 ← IO.monoNanosNow
  let ok ← force (checkTrace e.prog e.input t)
  failed := failed + (← report "checkTrace (= ValidExecution)" ok t6)
  let t6f ← IO.monoNanosNow
  failed := failed + (← report "fitsBy (= Fits)" (← force (fitsBy e.prog t pows)) t6f)
  let runCounts := countsOf (runCountTableBy e.prog t pows)
  let owed := jumpOwed runCounts
  let t6s ← IO.monoNanosNow
  failed := failed + (← report "stackFitsRowsB (= StackFits)"
    (← force (stackFitsRowsB e.prog t.κ runCounts)) t6s)
  IO.println s!"  κ = {t.κ}, run rows {fillTables.map runCounts}, JUMP owes {owed}, \
    least JUMP exponent {jumpHeight owed}"
  let t7 ← IO.monoNanosNow
  let main := e.traceInput.mainCounts
  let rowRegs (i : Fin 6) : Array (Regs K) :=
    e.rows[i].map fun (pc, fp) ↦ ⟨powAt pows pc, powAt pows fp⟩
  let replay ← force (mainRows e.prog t.image pows t.steps)
  let mainOk := match replay with
    | none => false
    | some acc => (List.finRange 6).all fun i ↦
        let file := (rowRegs i).extract 0 main[i]
        acc[i].size == main[i] && file.size == main[i] &&
          (acc[i].zip file).all fun (a, b) ↦ decide (a.pc = b.pc ∧ a.fp = b.fp)
  failed := failed + (← report "main rows = the replayed run, table by table, in order" mainOk t7)
  let t8 ← IO.monoNanosNow
  let sizesOk := (List.finRange 6).all fun i ↦ e.rows[i].size == e.traceInput.rowCounts[i]
  let fillStarts := (List.finRange 6).foldl (fun a i ↦ a ++ (rowRegs i).extract main[i]) #[]
  let fillOk ← force (fillRowsOk e.prog t.image pows fillStarts)
  failed := failed + (← report s!"fill rows ({fillStarts.size}) step to a permutation of themselves"
    (sizesOk && fillOk) t8)
  if opts.prod then
    let pcs := (e.rows.toList.flatMap fun rs ↦ rs.toList.map (·.1))
    let hints ← force (e.accessed.toList ++ pcs).mergeSort.eraseDups
    let t9 ← IO.monoNanosNow
    failed := failed + (← report s!"checkTrace with the Rust hints ({hints.length})"
      (← force (checkTrace e.prog e.input t hints)) t9)
  if opts.stages then stages e.prog e.input t
  if opts.gen || opts.prove then
    unless ← runGenerator gen opts.prove (2 ^ 24) 1 e.prog e.input t
      (if e.floor = 0 then some e.traceInput.rowCounts else none) do failed := failed + 1
  IO.println s!"  {failed} failed, {← since t0} s in all"
  return failed

end LeanerVMWitgen

open LeanerVMWitgen in
/-- `leanervm-witgen [--prod] [--hash] [--gen] [--prove] [--stages] file…`. -/
def main (args : List String) : IO UInt32 := do
  let opts : Options := {
    prod := args.contains "--prod",
    hash := args.contains "--hash", gen := args.contains "--gen",
    prove := args.contains "--prove", stages := args.contains "--stages" }
  let files := args.filter (!·.startsWith "--")
  if files.isEmpty then
    IO.eprintln "usage: leanervm-witgen [--prod] [--hash] [--gen] [--prove] [--stages] file…"
    return 2
  let mut failed := 0
  for file in files do
    failed := failed + (← runFile opts witnessGen file)
  IO.println s!"{failed} failed"
  return if failed = 0 then 0 else 1
