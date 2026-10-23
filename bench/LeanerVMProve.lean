/-
  LeanerVMProve

  The honest prover compiled into the `leanervm-prove` executable: a proof of the constraint
  statement tests' witness, timed phase by phase, written in the dump format of
  `scripts/dump-proof-rust.sh`, read back and checked by `verify` with its mutations.
-/

import LeanerVM.Protocol.Prove
import LeanerVMTests.Arithmetization.Statement
import LeanerVMTests.Protocol.Verify

/-!
# The `leanervm-prove` executable

`leanervm-prove [file] [rate] [fuel] [pure]` proves the hand-built leanISA witness of the
constraint statement tests (`LeanerVMTests.Arithmetization.Statement.fillW 1 g memCnt`, the
executor's `mul_192bit_word` with its fill blocks, `fill_satisfiedBy`) for its program
`fillProg` and public input `mulInput`, at the WHIR rate `rate` (default `1`) with `fuel`
candidate nonces per grind (default `2^24`). The witness's sizes are the smallest admissible:
memory `2^16`, a stack of `2^19` cells.

The run is the honest prover's writer (`Prove.writeProof` at `Prove.proveOps` and BLAKE2s-256)
in `IO`, with the time read at the first squeeze of each phase: the commitment, the bus phase,
the table sumcheck, the public input, the Flock phase, the opening's batching, WHIR and the
openings. The proof is written to `file` (default `tests/vectors/fill.proof`) in the text format
of `scripts/dump-proof-rust.sh`, read back by its loader (`RustProof.load`), and checked: `verify`
accepts it, and rejects each mutation of `Verify.mutationsOf` at the stage it names. With the
fourth argument `pure`, `prove` (the same prover in `Id`) runs too and must return the same proof.
The exit code is `1` if a check fails.
-/

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol
open LeanerVM.Protocol.Prove
open LeanerVM.Protocol.Verify LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Blake2sHash
open LeanerVMTests.Arithmetization.Statement LeanerVMTests.Protocol.RustProof
open LeanerVMTests.Protocol.Verify

namespace LeanerVMProve

/-! ## The dump format -/

/-- `n` as `w` hexadecimal digits. -/
def hexN (w n : ℕ) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- A word of `K`, 16 hexadecimal digits. -/
def hexWord (x : K) : String := hexN 16 x.toBitVec.toNat

/-- An element of `E`, its three limbs. -/
def hexElem (x : E) : String := s!"{hexWord (x.limb 0)} {hexWord (x.limb 1)} {hexWord (x.limb 2)}"

/-- A digest, its 32 bytes. -/
def hexDigestOf (d : Digest) : String :=
  String.join ((digestBytes d).map fun b ↦ hexN 2 b.toNat)

/-- The exponents of the first `2^12` powers of `g`, for printing operands. -/
def powers : Array K := Id.run do
  let mut a := #[]
  let mut x : K := 1
  for _ in [0:4096] do
    a := a.push x
    x := x * g
  return a

/-- The exponent `j` of an operand `g ^ j`, below `2^12`. -/
def exponentOf (x : K) : Option ℕ := powers.findIdx? (· == x)

/-- One instruction in the dump format, its operands as exponents. -/
def instrLine : Instr → Option String
  | .xor a b c => do return s!"xor {← exponentOf a} {← exponentOf b} {← exponentOf c}"
  | .mulNative a b c => do return s!"mul {← exponentOf a} {← exponentOf b} {← exponentOf c}"
  | .setConstant o k => do return s!"set {← exponentOf o} {hexElem k}"
  | .deref a b c m => do
    let mode := match m with
      | .cell => "cell"
      | .pc => "pc"
      | .fp => "fp"
    return s!"deref {← exponentOf a} {← exponentOf b} {← exponentOf c} {mode}"
  | .jump c d f => do return s!"jump {← exponentOf c} {← exponentOf d} {← exponentOf f}"
  | .blake2s om cv out md => do
    return s!"blake2s {← exponentOf (om 0)} {← exponentOf (om 1)} {← exponentOf (om 2)} " ++
      s!"{← exponentOf (om 3)} {← exponentOf cv} {← exponentOf out} {← exponentOf md}"

/-- A proof with its program and public input in the dump format of
`scripts/dump-proof-rust.sh`. -/
def dump (rate : ℕ) (prog : Program) (input : PublicInput) (p : Proof PrunedMerklePaths) :
    Option String := do
  let ops ← (List.finRange (2 ^ prog.logSize)).mapM fun i ↦ instrLine (prog.code i)
  let pub := s!"{hexElem (E.ofLimbs (input.lanes 0) (input.lanes 1) 0)} " ++
    hexElem (E.ofLimbs (input.lanes 2) (input.lanes 3) 0)
  let phase (o : PrunedMerklePaths) : List String :=
    s!"phase {o.leafData.length} {o.siblingHashes.length}" ::
      (o.leafData.map fun row ↦ s!"row {row.length} " ++ " ".intercalate (row.map hexWord)) ++
      o.siblingHashes.map fun h ↦ s!"sibling {hexDigestOf h}"
  let lines := ["leanvm-proof leanerVM", s!"rate {rate}", s!"program {ops.length}"] ++ ops ++
    [s!"program_hash {hexDigestOf (programHash prog)}", s!"public {pub}",
      s!"stream {p.stream.length}"] ++ p.stream.map hexElem ++
    [s!"merkle {p.merkle.length}"] ++ p.merkle.flatMap phase ++ ["end"]
  return "\n".intercalate lines ++ "\n"

/-! ## The phases' squeezes -/

/-- The walk's primitives counting squeezes, every read a placeholder. -/
def countOps : ChainOps (StateM ℕ) where
  nextScalar := pure 0
  sample := do modify (· + 1); pure 0
  nextRoot := pure default
  checkPow _ := pure 0
  nextOpening _ _ _ _ _ := pure []

/-- The squeezes a walk makes. -/
def squeezes {α : Type} (act : StateM ℕ α) : ℕ := (act.run 0).2

/-- The phases, each with the squeeze it starts at. -/
def phaseMarks (prog : Program) (s : Sizes) (input : PublicInput) : List (ℕ × String) :=
  let I := leanVm prog s
  let n₁ := squeezes (walkBus countOps I.μBus I.busClaims)
  let n₂ := squeezes (walkTables countOps I.τmax I.tableColumns)
  let n₃ := squeezes (walkPub countOps (PublicInput.sentCount I (I.publicLines input)))
  let n₄ := squeezes (walkFlock countOps (s.τ 5))
  [(0, "bus phase"), (n₁, "table sumcheck"), (n₁ + n₂, "public input"),
    (n₁ + n₂ + n₃, "Flock phase"), (n₁ + n₂ + n₃ + n₄, "opening batching"),
    (n₁ + n₂ + n₃ + n₄ + 1, "WHIR")]

/-! ## The run -/

/-- The primitives with the time printed at each phase's first squeeze. -/
def tapOps (ops : WireOps (ProveM IO)) (marks : List (ℕ × String)) (count last : IO.Ref ℕ)
    (phase : IO.Ref String) : WireOps (ProveM IO) :=
  { ops with
    sample := do
      let n ← count.modifyGet fun n ↦ (n, n + 1)
      if let some (_, name) := marks.find? (·.1 == n) then
        let t ← IO.monoNanosNow
        let t0 ← last.get
        IO.println s!"  {← phase.get}: {(t - t0).toFloat / 1e9} s"
        (← IO.getStdout).flush
        last.set t
        phase.set name
      ops.sample }

/-- Return a value through an opaque call, so that its computation stays inside a timed
interval. -/
@[noinline] def force {α : Type} (x : α) : IO α := pure x

/-- The witness, program and public input of the vectors. -/
def theWitness : Air.Flat.EnsembleWitness (leanIsaEnsemble fillProg) := fillW 1 g memCnt

/-- Run the prover in `IO` with the phases timed; the proof, or `none`. -/
def proveTimed (fuel ρ : ℕ) : IO (Option (Proof PrunedMerklePaths)) := do
  let some s := Sizes.ofWitness theWitness | do IO.println "no sizes"; return none
  if hs : s.Admissible fillProg ∧ validRate ρ then
    IO.println s!"sizes: memory 2^{s.logMem}, tables {List.ofFn s.τ}, stack 2^{stackMu fillProg s}, rate {ρ}"
    let t0 ← IO.monoNanosNow
    let q ← force (stackOf Blake2sFlock.blake2sFlockSpec fillProg s theWitness)
    let t1 ← IO.monoNanosNow
    IO.println s!"  the stack: {(t1 - t0).toFloat / 1e9} s"
    (← IO.getStdout).flush
    let count ← IO.mkRef 0
    let last ← IO.mkRef t1
    let phase ← IO.mkRef "the commitment"
    let H : List UInt8 → IO Digest := fun b ↦ pure (blake2sBytes b)
    let ops := tapOps (proveOps H fuel) (phaseMarks fillProg s mulInput) count last phase
    let p ← runProof fillProg mulInput
      (writeProof H ops Blake2sFlock.blake2sFlockSpec fillProg s hs.1 ρ hs.2 mulInput q)
    let t2 ← IO.monoNanosNow
    IO.println s!"  {← phase.get} and the openings: {(t2 - (← last.get)).toFloat / 1e9} s"
    IO.println s!"prover: {(t2 - t0).toFloat / 1e9} s in all"
    return p
  else
    IO.println "inadmissible sizes or rate"
    return none

end LeanerVMProve

open LeanerVMProve in
/-- `leanervm-prove [file] [rate] [fuel] [pure]`: prove the vectors' witness, write the proof,
read it back and check it. -/
def main (args : List String) : IO UInt32 := do
  let file := args.getD 0 "tests/vectors/fill.proof"
  let ρ := ((args[1]?).bind String.toNat?).getD 1
  let fuel := ((args[2]?).bind String.toNat?).getD (2 ^ 24)
  let some p ← proveTimed fuel ρ | do IO.println "the prover failed"; return 1
  IO.println s!"proof: {p.stream.length} scalars, openings of {p.merkle.map (·.leafData.length)} rows"
  let some text := dump ρ fillProg mulInput p | do IO.println "an operand has no exponent"; return 1
  IO.FS.writeFile file text
  IO.println s!"wrote {file}: {text.length} bytes"
  let mut failed := 0
  if args.getD 3 "" == "pure" then
    let t0 ← IO.monoNanosNow
    let p' ← force (prove fuel fillProg mulInput theWitness ρ)
    let t1 ← IO.monoNanosNow
    let same := p'.map (fun q ↦ q.stream == p.stream &&
      q.merkle.map (·.leafData) == p.merkle.map (·.leafData) &&
      q.merkle.map (fun o ↦ o.siblingHashes.map (·.toList)) ==
        p.merkle.map (fun o ↦ o.siblingHashes.map (·.toList)))
    IO.println s!"{if same == some true then "ok  " else "FAIL"} prove (in Id) returns the same proof, in {(t1 - t0).toFloat / 1e9} s"
    unless same == some true do failed := failed + 1
  let some f := load (← IO.FS.readFile file) | do IO.println "FAIL the loader rejects the file"; return 1
  let readBack := f.proof.stream == p.stream && f.prog.logSize == fillProg.logSize &&
    f.proof.merkle.map (·.leafData) == p.merkle.map (·.leafData) &&
    f.proof.merkle.map (fun o ↦ o.siblingHashes.map (·.toList)) ==
      p.merkle.map (fun o ↦ o.siblingHashes.map (·.toList))
  IO.println s!"{if readBack then "ok  " else "FAIL"} the loader reads the proof back"
  unless readBack do failed := failed + 1
  let t0 ← IO.monoNanosNow
  let ok ← force (verify f.prog f.input f.proof)
  let t1 ← IO.monoNanosNow
  IO.println s!"{if ok then "ok  " else "FAIL"} verify = {ok}, in {(t1 - t0).toFloat / 1e6} ms"
  unless ok do failed := failed + 1
  for m in mutationsOf f do
    let q := m.change f.proof
    let v := verify f.prog f.input q
    let o := outcomeOf f q
    let good := !v && o == m.expected
    unless good do failed := failed + 1
    let stage := ((reprStr o).replace "LeanerVMTests.Protocol.Verify.Outcome." "").replace
      "LeanerVM.Protocol.ReadError." ""
    IO.println s!"{if good then "ok  " else "FAIL"} {m.name}: verify = {v}, rejected at {stage}"
  IO.println s!"{failed} failed"
  return if failed = 0 then 0 else 1
