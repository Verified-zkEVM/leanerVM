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

/-!
# The `leanervm-witgen` executable

`leanervm-witgen [--prod] [--scan] [--hash] file…` reads each file written by
`scripts/dump-execution-rust.sh` (an execution of a compiled program by the Rust executor at
leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`, plain or `gzip`ped) and checks, each step
timed:

* the reading: the typed program (`Program`), the public input (`PublicInput`), the trace
  (`Trace prog`, through `TraceInput.adapt` from the image and the Rust counts), whose log-size and
  step count must be the file's;
* `SentinelSafe prog`, decided, and the fill blocks the Rust lists: each of the 48 pairs of table
  and size has a listed block whose slots hold the dummies and the closing jump (`IsFillBlock` at
  that start; a diagnostic of the listed starts, not a decision procedure for `HasFillBlocks`);
* with `--hash`, `programHash prog` against the Rust bytecode digest;
* the execution: `checkTraceGuess`, which is `checkTrace` with the address search taking an
  untrusted index guess from a table of powers (`checkTraceGuess_eq_checkTrace`, so it decides
  `ValidExecution`);
* the rows: the main run's states, replayed, are each table's first `main` rows in order, and the
  remaining rows of every table, the fill rows, step to a permutation of themselves away from the
  sentinel (`FillerRowsValid`, checked by sorting; a diagnostic, not proved equal to
  `checkFillerRows`);
* with `--prod`, the production `checkTrace` with the Rust hint list (the cells some row
  accessed and the row counters); with `--scan`, also with no hints (the exhaustive scan).

`runGenerator` is the hook for a witness generator of the shape `Generator`: generate, `prove`,
`verify`, each timed. The exit code is `1` if a check fails.
-/

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol
open LeanerVM.Protocol.Verify

namespace LeanerVMWitgen

/-! ## The address search from a guess -/

/-- The index of address `a` from an untrusted guess: the guess `i` is taken only when
`i < 2 ^ κ` and `g ^ i = a`, else the carrier's exhaustive scan. -/
def addressIndexGuess (κ : ℕ) (guess : K → Option ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  match guess a with
  | some i => if h : i < 2 ^ κ ∧ gpow i = a then some ⟨i, h.1⟩ else addressIndex κ [] a
  | none => addressIndex κ [] a

/-- The guessed search is the reference logarithm, for every guess. -/
theorem addressIndexGuess_eq {κ : ℕ} (hκ : κ < 64) (guess : K → Option ℕ) (a : K) :
    addressIndexGuess κ guess a = addressIndex κ [] a := by
  unfold addressIndexGuess
  split
  · split_ifs with h
    · rw [addressIndex_eq_gLog hκ]
      exact ((gLog?_spec hκ).mpr h.2.symm).symm
    · rfl
  · rfl

/-- Read the image through the guessed search. -/
def readGuess {κ : ℕ} (image : MemImage κ) (guess : K → Option ℕ) (a : K) : Option E :=
  (addressIndexGuess κ guess a).map image

/-- Fetch through the guessed search. -/
def fetchGuess (prog : Program) (guess : K → Option ℕ) (pc : K) : Option Instr :=
  (addressIndexGuess prog.logSize guess pc).map prog.code

/-- One checked step through the guessed search. -/
def stepGuess {κ : ℕ} (prog : Program) (image : MemImage κ) (guess : K → Option ℕ)
    (r : Regs K) : Option (Regs K) :=
  fetchGuess prog guess r.pc >>= executeWith (readGuess image guess) r

theorem stepGuess_eq {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ)
    (guess : K → Option ℕ) (r : Regs K) :
    stepGuess prog image guess r = stepChecked prog image [] r := by
  have hp : prog.logSize < 64 := lt_of_le_of_lt prog.logSize_le (by decide)
  have hr : readGuess image guess = readImage image [] := funext fun a ↦ by
    rw [readGuess, readImage, addressIndexGuess_eq hκ]
    rfl
  have hf : fetchGuess prog guess r.pc = fetchInstruction prog [] r.pc := by
    rw [fetchGuess, fetchInstruction, addressIndexGuess_eq hp]
    rfl
  rw [stepGuess, stepChecked, hf, hr]
  rfl

/-- `runToHalt` through the guessed search. -/
def runToHaltGuess {κ : ℕ} (prog : Program) (image : MemImage κ) (guess : K → Option ℕ) :
    ℕ → Regs K → Except CheckError ℕ
  | fuel, r =>
    if r.pc = prog.finalPc then
      if r.fp = 1 then .ok 0 else .error .finalFrame
    else match fuel with
      | 0 => .error .fuelExhausted
      | fuel + 1 => match stepGuess prog image guess r with
        | none => .error .invalidStep
        | some next => (runToHaltGuess prog image guess fuel next).map (· + 1)

theorem runToHaltGuess_eq {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ)
    (guess : K → Option ℕ) (fuel : ℕ) (r : Regs K) :
    runToHaltGuess prog image guess fuel r = runToHalt prog image [] fuel r := by
  induction fuel generalizing r with
  | zero => rw [runToHaltGuess, runToHalt]
  | succ fuel ih =>
    rw [runToHaltGuess, runToHalt, stepGuess_eq hκ]
    split_ifs
    · rfl
    · rfl
    · cases stepChecked prog image [] r with
      | none => rfl
      | some next => simp only [ih]

/-- `checkTrace` through the guessed search. -/
def checkTraceGuess (prog : Program) (input : PublicInput) (t : Trace prog)
    (guess : K → Option ℕ) : Bool :=
  decide ((if checkBoundary input (⟨t.κ, t.image, 0⟩ : Trace prog) then
    runToHaltGuess prog t.image guess t.steps Regs.initial else .error .publicBoundary) =
      .ok t.steps)

/-- The guessed check is the production check without hints, for every guess; so it holds
exactly on valid executions (`checkTrace_eq_true_iff`). -/
theorem checkTraceGuess_eq_checkTrace (prog : Program) (input : PublicInput) (t : Trace prog)
    (guess : K → Option ℕ) : checkTraceGuess prog input t guess = checkTrace prog input t [] := by
  unfold checkTraceGuess checkTrace checkWithinFuel
  split_ifs with hb
  · have hκ : t.κ < 64 :=
      lt_of_le_of_lt ((checkBoundary_eq_true_iff input _).mp hb).2.1 (by decide)
    rw [runToHaltGuess_eq hκ]
  · rfl

theorem checkTraceGuess_eq_true_iff (prog : Program) (input : PublicInput) (t : Trace prog)
    (guess : K → Option ℕ) :
    checkTraceGuess prog input t guess = true ↔ ValidExecution prog input t := by
  rw [checkTraceGuess_eq_checkTrace, checkTrace_eq_true_iff]

/-! ## The powers of `g` -/

/-- A word of `K` as a hash key. -/
def key (x : K) : UInt64 := x.toBitVec.toNat.toUInt64

/-- `g ^ 0, …, g ^ (n - 1)`. -/
def powersOf (n : ℕ) : Array K := Id.run do
  let mut a := Array.mkEmpty n
  let mut x : K := 1
  for _ in [0:n] do
    a := a.push x
    x := x * g
  return a

/-- The index of each power in the table, by its word. -/
def indexOf (pows : Array K) : Std.HashMap UInt64 ℕ := Id.run do
  let mut m : Std.HashMap UInt64 ℕ := Std.HashMap.emptyWithCapacity pows.size
  for h : i in [0:pows.size] do
    m := m.insert (key pows[i]) i
  return m

/-- The power `g ^ i`, from the table when it holds it. -/
def powAt (pows : Array K) (i : ℕ) : K := pows[i]?.getD (gpow i)

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
def instrOf (pows : Array K) : List String → ParseM Instr
  | ["xor", a, b, c] => do return .xor (← o a) (← o b) (← o c)
  | ["mul", a, b, c] => do return .mulNative (← o a) (← o b) (← o c)
  | ["set", a, k0, k1, k2] => do return .setConstant (← o a) (E.ofLimbs (← hexK k0) (← hexK k1) (← hexK k2))
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
    return (← hexK (String.ofList [cs.getD (2 * i) '0', cs.getD (2 * i + 1) '0'])).toBitVec.toNat.toUInt8
  return Blake2sHash.digestOfBytes bytes

/-- `n` lines read by `f`. -/
def many {α : Type} (n : ℕ) (f : List String → ParseM α) : ParseM (Array α) := do
  let mut a := Array.mkEmpty n
  for _ in [0:n] do
    a := a.push (← f (← words))
  return a

/-- Read a file; `pows` must hold the powers the operands name. -/
def parse (pows : Array K) : ParseM Execution := do
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
    unconstrainedReads := unconstrained, traceInput := ⟨memory, mainCounts, rowCounts, cycles⟩,
    accessed := accessed, rows := tables }

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
  let code (i : ℕ) : Option Instr := if h : i < 2 ^ prog.logSize then some (prog.code ⟨i, h⟩) else none
  let blockOk : ℕ × ℕ × ℕ → Bool := fun (p, s, t) ↦
    match opcodes[t]? with
    | none => false
    | some op => decide (p + s + 1 < 2 ^ prog.logSize) &&
        (List.range s).all (fun i ↦ code (p + i) == some (fillDummy op)) &&
        code (p + s) == some fillClose
  filler.all blockOk && opcodes.all fun op ↦ fillSizes.all fun s ↦
    filler.any fun (_, s', t) ↦ s' == s && opcodes[t]? == some op

/-- The main run replayed through the guessed search: each table's states in order; `none` on a
failed step. -/
def mainRows {κ : ℕ} (prog : Program) (image : MemImage κ) (guess : K → Option ℕ) (n : ℕ) :
    Option (Vector (Array (Regs K)) 6) := Id.run do
  let mut acc : Vector (Array (Regs K)) 6 := Vector.replicate 6 #[]
  let mut r := Regs.initial
  for _ in [0:n] do
    let some ins := fetchGuess prog guess r.pc | return none
    let i := tableOf ins.opcode
    acc := acc.set i (acc[i].push r)
    let some next := executeWith (readGuess image guess) r ins | return none
    r := next
  return some acc

/-- Two states as a sort key. -/
def regsKey (r : Regs K) : UInt64 × UInt64 := (key r.pc, key r.fp)

/-- Lexicographic order on keys. -/
def keyLt (a b : UInt64 × UInt64) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- The fill rows: away from the sentinel, each steps, and the successors are a permutation of
the starts (compared sorted). -/
def fillRowsOk {κ : ℕ} (prog : Program) (image : MemImage κ) (guess : K → Option ℕ)
    (starts : Array (Regs K)) : Bool := Id.run do
  let mut next : Array (UInt64 × UInt64) := Array.mkEmpty starts.size
  for r in starts do
    if r.pc = prog.finalPc then return false
    let some s := stepGuess prog image guess r | return false
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

/-- Generate a witness, prove at rate `ρ` with `fuel` nonces a grind, verify; each timed. -/
def runGenerator (gen : Generator) (fuel ρ : ℕ) (prog : Program) (input : PublicInput)
    (t : Trace prog) : IO Bool := do
  let t0 ← IO.monoNanosNow
  match gen prog input t with
  | none =>
    IO.println s!"FAIL the generator returned none, in {← since t0} s"
    return false
  | some w =>
  IO.println s!"  generate: {← since t0} s"
  let t1 ← IO.monoNanosNow
  let some p ← force (prove fuel prog input w ρ) | do
    IO.println s!"FAIL prove returned none, in {← since t1} s"
    return false
  IO.println s!"  prove: {p.stream.length} scalars, in {← since t1} s"
  let t2 ← IO.monoNanosNow
  let ok ← force (verify prog input p)
  IO.println s!"{if ok then "ok  " else "FAIL"} verify = {ok}, in {← since t2} s"
  return ok

/-! ## The run -/

/-- The options of a run. -/
structure Options where
  /-- Run the production `checkTrace` with the Rust hint list. -/
  prod : Bool := false
  /-- Also run it with no hints. -/
  scan : Bool := false
  /-- Check the program hash. -/
  hash : Bool := false

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
def runFile (opts : Options) (gen? : Option Generator) (file : String) : IO ℕ := do
  IO.println s!"== {file}"
  let t0 ← IO.monoNanosNow
  let text ← readText file
  let lines := (text.splitOn "\n").toArray
  let (b, κ) := sizesOf lines
  let pows ← force (powersOf (max b (2 ^ min κ 40)))
  let index ← force (indexOf pows)
  let guess : K → Option ℕ := fun a ↦ index[key a]?
  IO.println s!"  read {text.length} bytes, powers of g to 2^{Nat.log 2 pows.size}: {← since t0} s"
  let t1 ← IO.monoNanosNow
  let e ← match (parse pows).run 0 |>.run lines with
    | .ok (e, _) => pure e
    | .error msg => do IO.println s!"FAIL parse: {msg}"; return 1
  IO.println s!"  {e.name} (leanVM {e.pin.take 8}): program 2^{e.prog.logSize}, memory 2^{e.κ}, \
    steps {e.steps}, cycles {e.traceInput.cycles}, main {e.traceInput.mainCounts.toList}, \
    rows {e.traceInput.rowCounts.toList}, unconstrained reads {e.unconstrainedReads}"
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
  if opts.hash then
    let t5 ← IO.monoNanosNow
    failed := failed + (← report "programHash = the Rust bytecode digest"
      (programHash e.prog == e.programHash) t5)
  let t6 ← IO.monoNanosNow
  let ok ← force (checkTraceGuess e.prog e.input t guess)
  failed := failed + (← report "checkTraceGuess (= ValidExecution)" ok t6)
  let t7 ← IO.monoNanosNow
  let main := e.traceInput.mainCounts
  let rowRegs (i : Fin 6) : Array (Regs K) :=
    e.rows[i].map fun (pc, fp) ↦ ⟨powAt pows pc, powAt pows fp⟩
  let replay ← force (mainRows e.prog t.image guess t.steps)
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
  let fillOk ← force (fillRowsOk e.prog t.image guess fillStarts)
  failed := failed + (← report s!"fill rows ({fillStarts.size}) step to a permutation of themselves"
    (sizesOk && fillOk) t8)
  if opts.prod then
    let pcs := (e.rows.toList.flatMap fun rs ↦ rs.toList.map (·.1))
    let hints := (e.accessed.toList ++ pcs).mergeSort.eraseDups
    let t9 ← IO.monoNanosNow
    failed := failed + (← report s!"checkTrace with the Rust hints ({hints.length})"
      (← force (checkTrace e.prog e.input t hints)) t9)
  if opts.scan then
    let t10 ← IO.monoNanosNow
    failed := failed + (← report "checkTrace with no hints" (← force (checkTrace e.prog e.input t [])) t10)
  match gen? with
  | some gen => unless ← runGenerator gen (2 ^ 24) 1 e.prog e.input t do failed := failed + 1
  | none => IO.println "  no generator linked"
  IO.println s!"  {failed} failed, {← since t0} s in all"
  return failed

end LeanerVMWitgen

open LeanerVMWitgen in
/-- `leanervm-witgen [--prod] [--scan] [--hash] file…`. -/
def main (args : List String) : IO UInt32 := do
  let opts : Options := {
    prod := args.contains "--prod", scan := args.contains "--scan",
    hash := args.contains "--hash" }
  let mut failed := 0
  for file in args.filter (!·.startsWith "--") do
    failed := failed + (← runFile opts none file)
  IO.println s!"{failed} failed"
  return if failed = 0 then 0 else 1
