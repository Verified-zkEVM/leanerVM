import LeanerVM.Protocol.Verify.Setup
import LeanerVMTests.Protocol.RustProofData

/-!
# The Rust proof fixture

`scripts/dump-proof-rust.sh` (leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`) proves the
division program of the pinned Rust test suite (`crates/lean_compiler/tests/suite/field_div.rs`,
with its fill blocks) at the test rate and prints the program, the hash of its bytecode table,
the public input, the scalar stream and the pruned Merkle opening phases as text
(`RustProofData.rustProofText`). `load` reads it: an operand exponent `j` is the operand
`g ^ j`, an immediate is three limbs, a public word is its two low limbs (a nonzero third limb
does not load), a digest is its 32 bytes. The program the loader builds
hashes to the Rust's program hash, which pins the reading of every instruction.

The setup on the fixture: the announced sizes and rate are admissible; they fix a stack of
`2^20` cells of which 33 lanes are committed, a WHIR ladder of four levels querying
`224, 56, 32, 22` positions, and a bus of depth 18 with five boundary columns, as the second
verifier reads them (`python-verifier/verifier.py:1373-1385`). Each setup check rejects its
mutation before any hash: a nonzero upper limb in an announced size, a size above its cap, the
`BLAKE2S` table below its floor, a rate outside its window. The chain walk's setup reads the
root, and rejects a nonzero third limb in a half of it.
-/

namespace LeanerVMTests.Protocol.RustProof

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Verify
open LeanerVMTests.Protocol.RustProofData

/-! ## The loader -/

/-- A hexadecimal digit. -/
def hexDigit (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- A hexadecimal numeral. -/
def hexNat (s : String) : Option ℕ :=
  s.foldl (fun acc c ↦ acc.bind fun n ↦ (hexDigit c).map (16 * n + ·)) (some 0)

/-- A word of `K` from 16 hexadecimal digits. -/
def hexK (s : String) : Option K := (hexNat s).map K.ofBits

/-- An element of `E` from its three limbs. -/
def hexE (a b c : String) : Option E := do
  return E.ofLimbs (← hexK a) (← hexK b) (← hexK c)

/-- A digest from its 32 bytes in 64 hexadecimal digits. -/
def hexDigest (s : String) : Option Digest := do
  let cs := s.toList
  if cs.length ≠ 64 then none
  let bytes ← (List.range 32).mapM fun i ↦
    (hexNat (String.ofList [cs.getD (2 * i) '0', cs.getD (2 * i + 1) '0'])).map (·.toUInt8)
  return digestOfBytes bytes

/-- A decimal numeral. -/
def dec (s : String) : Option ℕ := s.toNat?

/-- The operand `g ^ j` of an exponent. -/
def operand (s : String) : Option K := (dec s).map gpow

/-- One instruction of the dump: an opcode and its operand exponents (`Op`,
`crates/lean_vm/src/cpu/isa.rs:6-56`). -/
def instr : List String → Option Instr
  | ["xor", a, b, c] => do return .xor (← operand a) (← operand b) (← operand c)
  | ["mul", a, b, c] => do return .mulNative (← operand a) (← operand b) (← operand c)
  | ["set", o, k0, k1, k2] => do return .setConstant (← operand o) (← hexE k0 k1 k2)
  | ["deref", o1, o2, o3, m] => do
    let mode ← match m with
      | "cell" => some DerefMode.cell
      | "pc" => some .pc
      | "fp" => some .fp
      | _ => none
    return .deref (← operand o1) (← operand o2) (← operand o3) mode
  | ["jump", c, d, f] => do return .jump (← operand c) (← operand d) (← operand f)
  | ["blake2s", i0, i1, i2, i3, cv, out, md] => do
    return .blake2s ![← operand i0, ← operand i1, ← operand i2, ← operand i3] (← operand cv)
      (← operand out) (← operand md)
  | _ => none

/-- A program of `2 ^ k` instructions, `k ≤ 32`. -/
def programOf (ops : Array Instr) : Option Program :=
  let k := Nat.log 2 ops.size
  if h : k ≤ maxLogBytecode ∧ 2 ^ k = ops.size then
    some ⟨k, h.1, fun i ↦ ops.getD i.val (.xor 0 0 0)⟩
  else none

/-- What the dump holds. -/
structure Fixture where
  /-- The WHIR rate exponent the proof was made at. -/
  rate : ℕ
  /-- The program. -/
  prog : Program
  /-- The Rust's hash of its bytecode table. -/
  programHash : Digest
  /-- The public input. -/
  input : PublicInput
  /-- The proof. -/
  proof : Proof PrunedMerklePaths

/-- The `n` lines after the first of `ls`, read by `f`, and the rest. -/
def takeLines {α : Type} (f : List String → Option α) (n : ℕ) (ls : List (List String)) :
    Option (List α × List (List String)) := do
  let xs ← (ls.take n).mapM f
  if xs.length = n then some (xs, ls.drop n) else none

/-- One scalar line. -/
def scalarLine : List String → Option E
  | [a, b, c] => hexE a b c
  | _ => none

/-- One row line: its width, then its words. -/
def rowLine : List String → Option (List K)
  | "row" :: n :: ws => do
    let row ← ws.mapM hexK
    if row.length = (← dec n) then some row else none
  | _ => none

/-- One sibling line. -/
def siblingLine : List String → Option Digest
  | ["sibling", h] => hexDigest h
  | _ => none

/-- The opening phases. -/
def phases : ℕ → List (List String) → Option (List PrunedMerklePaths × List (List String))
  | 0, ls => some ([], ls)
  | n + 1, ["phase", r, s] :: ls => do
    let (rows, ls) ← takeLines rowLine (← dec r) ls
    let (sibs, ls) ← takeLines siblingLine (← dec s) ls
    let (rest, ls) ← phases n ls
    return (⟨rows, sibs⟩ :: rest, ls)
  | _, _ => none

/-- Read the dump. -/
def load (text : String) : Option Fixture := do
  let ls := ((text.splitOn "\n").map fun l ↦ (l.splitOn " ").filter (· ≠ "")).filter (· ≠ [])
  match ls with
  | ["leanvm-proof", _] :: ["rate", r] :: ["program", n] :: ls =>
    let (ops, ls) ← takeLines instr (← dec n) ls
    let prog ← programOf ops.toArray
    match ls with
    | ["program_hash", h] :: ["public", a0, a1, a2, b0, b1, b2] :: ["stream", n] :: ls =>
      let w0 ← hexE a0 a1 a2
      let w1 ← hexE b0 b1 b2
      -- `PublicInput` has no third limbs; the Rust verifier rejects nonzero ones
      -- (`crates/lean_vm/src/cpu/mod.rs:141`).
      if w0.limb 2 ≠ 0 ∨ w1.limb 2 ≠ 0 then none
      let (stream, ls) ← takeLines scalarLine (← dec n) ls
      match ls with
      | ["merkle", p] :: ls =>
        let (merkle, ls) ← phases (← dec p) ls
        if ls ≠ [["end"]] then none
        return ⟨← dec r, prog, ← hexDigest h,
          ⟨![w0.limb 0, w0.limb 1, w1.limb 0, w1.limb 1]⟩, ⟨stream, merkle⟩⟩
      | _ => none
    | _ => none
  | _ => none

/-- The fixture. -/
def fixture? : Option Fixture := load rustProofText

/-- The fixture, or a placeholder the tests below reject. -/
def fx : Fixture :=
  fixture?.getD ⟨0, ⟨0, by decide, fun _ ↦ .xor 0 0 0⟩, Vector.replicate 8 0, ⟨fun _ ↦ 0⟩, ⟨[], []⟩⟩

/-! ## The fixture -/

#guard fixture?.isSome
#guard fx.prog.logSize == 11
#guard fx.proof.stream.length == 770
#guard fx.proof.merkle.map (·.leafData.length) == [223, 56, 32, 22]
#guard fx.proof.merkle.map (·.siblingHashes.length) == [1459, 422, 235, 154]

-- The loaded program hashes to the Rust's program hash.
#guard (programHash fx.prog).toList == fx.programHash.toList

-- The public input `[g^20, 1]`.
#guard fx.input.lanes 0 == gpow 20 && fx.input.lanes 1 == 0 && fx.input.lanes 2 == 1 &&
  fx.input.lanes 3 == 0

/-- The fixture with its public line replaced. -/
def withPublic (line : String) : String :=
  rustProofText.replace "public 0000000000100000 0000000000000000 0000000000000000 \
    0000000000000001 0000000000000000 0000000000000000" line

-- A nonzero third limb in either public word does not load.
#guard (load (withPublic "public 100000 0 1 1 0 0")).isNone
#guard (load (withPublic "public 100000 0 0 1 0 1")).isNone
#guard (load (withPublic "public 100000 0 0 1 0 0")).isSome

/-! ## The setup -/

/-- The announced sizes and rate. -/
def sizes : Sizes × ℕ := (setup? fx.prog fx.proof).getD (⟨1, by decide, fun _ ↦ 0⟩, 0)

#guard (setup? fx.prog fx.proof).isSome
#guard sizes.1.logMem == 17 && List.ofFn sizes.1.τ == [0, 3, 3, 1, 4, 3] && sizes.2 == 1
#guard stackMu fx.prog sizes.1 == 20
#guard nLanes fx.prog sizes.1 == 33
#guard ((ladderOf fx.prog sizes.1 sizes.2).getD []).map (·.fold) == [6, 4, 4, 4]
#guard ((ladderOf fx.prog sizes.1 sizes.2).getD []).map (·.queries) == [224, 56, 32, 22]
#guard (leanVm fx.prog sizes.1).μBus == 18
#guard (leanVm fx.prog sizes.1).busClaims == 5
#guard (leanVm fx.prog sizes.1).τmax == 4
#guard (leanVm fx.prog sizes.1).tableColumns == 104

/-- The proof with stream scalar `i` replaced. -/
def withScalar (i : ℕ) (x : E) : Proof PrunedMerklePaths :=
  ⟨fx.proof.stream.set i x, fx.proof.merkle⟩

-- A nonzero upper limb in an announced size.
#guard (setup? fx.prog (withScalar 2 (E.ofLimbs (K.ofBits 3) 0 1))).isNone
-- A size above its cap: a table of `2^33` rows.
#guard (setup? fx.prog (withScalar 2 (sizeScalar 33))).isNone
-- The `BLAKE2S` table below its floor of `2^3` rows.
#guard (setup? fx.prog (withScalar 6 (sizeScalar 2))).isNone
-- The memory below its window.
#guard (setup? fx.prog (withScalar 0 (sizeScalar 15))).isNone
-- A stack above `2^28` cells: the memory at `2^28`.
#guard (setup? fx.prog (withScalar 0 (sizeScalar 28))).isNone
-- A rate outside its window.
#guard (setup? fx.prog (withScalar 7 (sizeScalar 5))).isNone
#guard (setup? fx.prog (withScalar 7 (sizeScalar 0))).isNone

/-! ## The setup's reads -/

/-- The chain state after the seed. -/
def seed : FsState := FsState.seed fx.prog fx.input

/-- The setup's reads on a stream. -/
def runSetup (stream : List E) : Except ReadError Digest :=
  (((walkSetup (readerOps (m := Id) blake2sBytes)).run' ⟨seed, stream, []⟩).run : Id _)

-- The root is the two scalars after the sizes.
#guard match runSetup fx.proof.stream with
  | .ok d => digestScalars d == (fx.proof.stream[8]!, fx.proof.stream[9]!)
  | .error _ => false

-- A nonzero third limb in a half of the root.
#guard match runSetup ((fx.proof.stream.set 9 (fx.proof.stream[9]! + E.ofLimbs 0 0 1))) with
  | .error .nonCanonicalEncoding => true
  | _ => false

end LeanerVMTests.Protocol.RustProof
