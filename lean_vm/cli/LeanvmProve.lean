import Statement.Prover.Prove
import LeanVM.Protocol.Verifier

/-!
# `leanvm-prove`: the statement's honest prover on a program, an input and a trace

`lake exe leanvm-prove <case dir> [fuel]` reads, from the case directory
(`scripts/export-prover-traces-rust.sh` writes them):

* `bytecode.bin`: the program's bytecode table (the sixteen slots of every instruction, slot by
  slot), decoded into a `Program` (`decodeProgram`, checked to re-encode to the same words);
* `public_input.bin`: the public input's 32 bytes;
* `memory.bin`: the execution's memory, 24 bytes per cell;
* `trace.txt`: `<log2 cells> <steps> <rate>`;

runs `LeanVM.Prover.prove` with Keccak-256 and Keccak-f[1600] (the deployed hashes, `Id`) at
`fuel` nonces per proof of work (default `2^25`), and writes the proof in the four-file format
of the Rust prover's fixtures (`lean_stream.bin`, `lean_merkle_openings.bin` in the case
directory), which `leanvm-verify` and the Rust verifier read. It prints the time taken.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

namespace LeanvmProve

/-- The opcode of a code. -/
def opcodeOf? (c : K) : Option Opcode :=
  [Opcode.xor, .mulNative, .setConstant, .deref, .jump, .keccak].find? (·.code = c)

/-- A flag word. -/
def flagOf? (c : K) : Option Bool :=
  if c = 0 then some false else if c = 1 then some true else none

/-- The `DEREF` mode of its two flags. -/
def derefModeOf? (fpc ffp : K) : Option DerefMode :=
  if fpc = 0 ∧ ffp = 0 then some .cell
  else if fpc = 1 ∧ ffp = 0 then some .pc
  else if fpc = 0 ∧ ffp = 1 then some .fp
  else none

/-- The instruction of a bus entry (the inverse of `entry`, where it is one). -/
def instrOf? (e : Array K) : Option Instr := do
  let op ← opcodeOf? (e.getD 0 0)
  let x (i : ℕ) : K := e.getD i 0
  match op with
  | .xor => some (.xor (x 1) (x 2) (x 3))
  | .mulNative => some (.mulNative (x 1) (x 2) (x 3))
  | .setConstant => some (.setConstant (x 1) (E.ofLimbs (x 2) (x 3) (x 4)))
  | .deref => do
    let mode ← derefModeOf? (x 4) (x 5)
    some (.deref (x 1) (x 2) (x 3) mode)
  | .jump => some (.jump (x 1) (x 2) (x 3))
  | .keccak => do
    let inOdd ← flagOf? (x 9)
    let outOdd ← flagOf? (x 10)
    some (.keccak ![x 1, x 2, x 3, x 4] (x 5) (x 6) (x 7) (x 8) inOdd outOdd)

/-- The program a bytecode table encodes: `16 · 2^logSize` words, word `i + 2^logSize · s` slot
`s` of instruction `i`; checked to re-encode to the same words. -/
def decodeProgram (words : Array K) : Except String Program := do
  let n := words.size / 16
  let logSize := Nat.log2 n
  unless 16 * 2 ^ logSize = words.size do throw "the bytecode is not 16 · 2^k words"
  if h : logSize ≤ maxLogBytecode then
    let mut code : Array Instr := #[]
    for i in [0:n] do
      let e := (Array.range 11).map fun j ↦ words.getD (i + n * (3 + j)) 0
      match instrOf? e with
      | some ins => code := code.push ins
      | none => throw s!"instruction {i} does not decode"
    let prog : Program := ⟨logSize, h, fun i ↦ code.getD i.val (.jump 0 0 0)⟩
    unless (LeanVM.bytecodeWords prog).toArray == words do throw "the bytecode does not re-encode"
    return prog
  else throw "the bytecode is too long"

/-- Little-endian bytes of a word. -/
def wordLE (w : UInt64) : List UInt8 := (List.range 8).map fun i ↦ (w >>> (8 * i).toUInt64).toUInt8

/-- The bytes of a scalar: three limbs, little-endian. -/
def scalarBytes (x : E) : List UInt8 :=
  wordLE (x.limb 0).lane ++ wordLE (x.limb 1).lane ++ wordLE (x.limb 2).lane

/-- The memory of 24 bytes per cell. -/
def decodeMemory (b : ByteArray) : Array E :=
  let lane (o : ℕ) : UInt64 :=
    (List.range 8).foldr (fun i acc ↦ (acc <<< 8) ||| (b.get! (o + i)).toUInt64) 0
  (Array.range (b.size / 24)).map fun i ↦
    E.ofLimbs (K.ofLane (lane (24 * i))) (K.ofLane (lane (24 * i + 8)))
      (K.ofLane (lane (24 * i + 16)))

def main (args : List String) : IO UInt32 := do
  match args with
  | dir :: rest =>
    let fuel := (rest.head?.bind String.toNat?).getD (2 ^ 25)
    let read := fun (p : String) => do return (← IO.FS.readBinFile (dir ++ "/" ++ p)).toList
    let some words := decodeWords (← read "bytecode.bin") | do IO.eprintln "bad bytecode"; return 2
    let some digest := decodeDigest (← read "public_input.bin") | do
      IO.eprintln "bad public input"; return 2
    let prog ← match decodeProgram words.toArray with
      | .ok p => pure p
      | .error e => do IO.eprintln e; return 2
    let input : PublicInput := ⟨fun i ↦ K.ofLane digest[i]⟩
    let mem := decodeMemory (← IO.FS.readBinFile (dir ++ "/memory.bin"))
    let nums := (((← IO.FS.readFile (dir ++ "/trace.txt")).trimAscii.toString.splitOn " ")).filterMap String.toNat?
    let [κ, steps, ρ] := nums | do IO.eprintln "bad trace.txt"; return 2
    unless mem.size = 2 ^ κ do IO.eprintln "the memory is not 2^κ cells"; return 2
    let t : Trace prog := ⟨κ, fun i ↦ mem.getD i.val 0, steps⟩
    let start ← IO.monoMsNow
    let proof := LeanVM.Prover.prove (m := Id) keccak256 keccakF prog input t ρ fuel
    let stream := proof.stream.flatMap scalarBytes
    let openings := proof.openings.flatMap fun o ↦ o.leaf.flatMap kBytes ++ o.path.flatMap digestBytes
    IO.FS.writeBinFile (dir ++ "/lean_stream.bin") ⟨stream.toArray⟩
    IO.FS.writeBinFile (dir ++ "/lean_merkle_openings.bin") ⟨openings.toArray⟩
    let stop ← IO.monoMsNow
    IO.println s!"{dir}: {proof.stream.length} scalars, {proof.openings.length} openings, \
      {(stop - start).toFloat / 1000} s"
    return (if proof.stream.isEmpty then 1 else 0)
  | _ =>
    IO.eprintln "usage: leanvm-prove <case dir> [fuel]"
    return 2

end LeanvmProve

def main (args : List String) : IO UInt32 := LeanvmProve.main args
