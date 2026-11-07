import LeanVM.Protocol.Verifier
import LeanVM.Wire.Encoding

/-!
# `leanvm-verify`: the deployed verifier on a proof's files

Three forms, on the files the Rust prover writes (`scripts/export-verifier-fixtures-rust.sh`);
each prints the verdict, and the exit code is `0` on acceptance. `scripts/fuzz-verifier.py`
compares them with the Rust verifier (`scripts/rust-verifier-cli`, its two forms) and the Python
verifier on mutated proofs.

* `lake exe leanvm-verify <bytecode> <public input> <stream> <merkle phases>`: the proof in its
  structured form, the Rust `Proof` (`crates/verifier/src/transcript.rs:10-16`): the scalars
  (`stream.bin`) and the phases of unpruned Merkle paths (`merkle_phases.bin`, `readPhasesFile`);
  runs `Verifier.verify` (`LeanVM/Facts/Verifier.lean`, the statement's verifier compiled, on the
  program's bytecode words) on it.
* `lake exe leanvm-verify <bytecode> <public input> <proof wire>`: the proof's one wire encoding
  (`Proof::to_bytes`, `crates/fiat_shamir/src/wire.rs`, `proof.wire`), decoded with
  `Proof.fromBytes` (`LeanVM/Wire/Encoding.lean`) over Keccak-f[1600], a proof that does not
  decode rejected, as `LeanVM.leanVmVerifierOnBytes` (`LeanVM/Wire/Statements.lean`) does, then
  `Verifier.verify` on the decoded proof.
* `lake exe leanvm-verify --flat <bytecode> <public input> <stream> <merkle openings>`:
  `LeanVM.Protocol.Verifier.verifyFiles`, the Lean transcription of `python-verifier/verifier.py`,
  on the Python's four files (`merkle_openings.bin`: every opening, its eight-byte position, its
  leaf and its siblings, `verifier.py:433-445`).
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

namespace LeanvmVerify

/-- A little-endian number of `size` bytes at `pos`, and the position after it; `none` past the
end. -/
def readLE (b : ByteArray) (size pos : ℕ) : Option (ℕ × ℕ) :=
  if pos + size ≤ b.size then
    some ((List.range size).foldr (fun i acc ↦ acc * 256 + (b.get! (pos + i)).toNat) 0,
      pos + size)
  else none

/-- `count` values read one after the other by `read`. -/
def readCount {α : Type} (read : ℕ → Option (α × ℕ)) : ℕ → ℕ → Option (List α × ℕ)
  | 0, pos => some ([], pos)
  | count + 1, pos => do
    let (a, pos) ← read pos
    let (rest, pos) ← readCount read count pos
    some (a :: rest, pos)

/-- The bytes `[pos, pos + size)` as a list. -/
def slice (b : ByteArray) (pos size : ℕ) : List UInt8 :=
  (b.extract pos (pos + size)).toList

/-- One Merkle path of `merkle_phases.bin`: its `u64` position, its `u32` leaf length and that
many `u64` words, its `u32` sibling count and that many 32-byte digests. -/
def readPath (b : ByteArray) (pos : ℕ) : Option (Opening × ℕ) := do
  let (leafIndex, pos) ← readLE b 8 pos
  let (leafLength, pos) ← readLE b 4 pos
  let (leaf, pos) ← readCount (fun pos ↦ (readLE b 8 pos).map fun (w, p) ↦
    (K.ofLane (UInt64.ofNat w), p)) leafLength pos
  let (siblingCount, pos) ← readLE b 4 pos
  let (path, pos) ← readCount (fun pos ↦
    if pos + 32 ≤ b.size then some (digestOfBytes (slice b pos 32), pos + 32) else none)
    siblingCount pos
  some (⟨leafIndex, leaf, path⟩, pos)

/-- One phase: its `u32` path count, then the paths. -/
def readPhase (b : ByteArray) (pos : ℕ) : Option (List Opening × ℕ) := do
  let (count, pos) ← readLE b 4 pos
  readCount (readPath b) count pos

/-- **`merkle_phases.bin`**, the Rust `Vec<Vec<MerklePath>>`, all little-endian: the `u32` phase
count, then the phases; trailing bytes or a short read are refused. -/
def readPhasesFile (b : ByteArray) : Option (List (List Opening)) := do
  let (count, pos) ← readLE b 4 0
  let (phases, pos) ← readCount (readPhase b) count pos
  if pos = b.size then some phases else none

/-- **The verifier on the structured proof**: decode the bytecode, the public input, the scalars
and the phases, and run `verify`; anything that does not decode is rejected. -/
def verifyStructured (bytecode publicInput stream : List UInt8) (phases : ByteArray) : Bool :=
  match decodeWords bytecode, decodeDigest publicInput, decodeScalars stream,
      readPhasesFile phases with
  | some words, some digest, some scalars, some openings => verify words digest ⟨scalars, openings⟩
  | _, _, _, _ => false

/-- **The verifier on the wire**: decode the bytecode, the public input and the proof's bytes
(`Proof.fromBytes`), and run `verify`; anything that does not decode is rejected. -/
def verifyWire (bytecode publicInput proof : List UInt8) : Bool :=
  match decodeWords bytecode, decodeDigest publicInput,
      Id.run (Proof.fromBytes (m := Id) keccakF1600 proof) with
  | some words, some digest, some π => verify words digest π
  | _, _, _ => false

/-- The driver. -/
def main (args : List String) : IO UInt32 := do
  let read := fun (p : String) => do return (← IO.FS.readBinFile p).toList
  let verdict (ok : Bool) : IO UInt32 := do
    if ok then
      IO.println "verification succeeded"
      return 0
    else
      IO.println "verification failed"
      return 1
  match args with
  | ["--flat", bytecode, publicInput, stream, openings] =>
    verdict (verifyFiles (← read bytecode) (← read publicInput) (← read stream) (← read openings))
  | [bytecode, publicInput, stream, phases] =>
    verdict (verifyStructured (← read bytecode) (← read publicInput) (← read stream)
      (← IO.FS.readBinFile phases))
  | [bytecode, publicInput, proof] =>
    verdict (verifyWire (← read bytecode) (← read publicInput) (← read proof))
  | _ =>
    IO.eprintln "usage: leanvm-verify <bytecode> <public input> (<stream> <merkle phases> | \
      <proof wire>) | --flat <bytecode> <public input> <stream> <merkle openings>"
    return 2

end LeanvmVerify

def main (args : List String) : IO UInt32 := LeanvmVerify.main args
