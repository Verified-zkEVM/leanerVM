/-
  LeanerVMBench

  Steady-state timings of the field arithmetic, the BLAKE2s hasher, a Merkle root and a
  multilinear evaluation, as compiled into the `leanervm-bench` executable.
-/

import LeanerVM.Protocol.Field
import LeanerVM.Protocol.Merkle

/-!
# The `leanervm-bench` executable

Each workload runs a fixed number of iterations, scaled by the first argument, a percentage
(default `100`), on
inputs derived from the seed in `LEANERVM_BENCH_SEED` (default `12345`), so that nothing is
evaluated at compile time. Every result feeds a printed checksum, and every timed value is passed
through the opaque `force` inside the timed interval. See `bench/README.md`.
-/

namespace LeanerVMBench

open LeanerVM.Parameters LeanerVM.Protocol CompPoly

/-- A xorshift step, for inputs the compiler cannot precompute. -/
def xs (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A `K` word from a seed. -/
def kOf (s : UInt64) : K := BF64.ofBitVec s.toBitVec

/-- An `E` element from a seed. -/
def eOf (s : UInt64) : E := E.ofLimbs (kOf s) (kOf (xs s)) (kOf (xs (xs s)))

/-- Return a value through an opaque call, so that its computation stays inside the timed
interval. -/
@[noinline] def force {α : Type} (x : α) : IO α := pure x

/-- Print one result line: nanoseconds per operation and a checksum. -/
def report (name : String) (iters : Nat) (t0 t1 : Nat) (check : String) : IO Unit := do
  let ns := (t1 - t0).toFloat / iters.toFloat
  IO.println s!"{name}\t{ns} ns/op\t{iters} iterations\t[{check}]"

/-- Time `iters` runs of a step on an accumulator. -/
def timeLoop {α : Type} (name : String) (iters : Nat) (init : α) (step : Nat → α → α)
    (show_ : α → String) : IO Unit := do
  let mut acc ← force init
  let t0 ← IO.monoNanosNow
  for i in [0:iters] do
    acc ← force (step i acc)
  let t1 ← IO.monoNanosNow
  report name iters t0 t1 (show_ acc)

/-- The inverse through a field dictionary, the way generic code such as interpolation reaches
it. -/
@[noinline, nospecialize] def fieldInv {R : Type} [Field R] (x : R) : R := x⁻¹

/-- Bytes from a seed. -/
def bytesOf (seed : UInt64) (len : Nat) : List UInt8 :=
  (List.range len).map fun i ↦ (xs (seed + i.toUInt64)).toUInt8

/-- All workloads, with iteration counts scaled to `percent` per cent. -/
def run (seed : UInt64) (percent : Nat) : IO Unit := do
  let n (base : Nat) : Nat := max 1 (base * percent / 100)
  let kHex (a : K) : String := a.toBitVec.toHex
  -- K
  let b := kOf (xs seed)
  timeLoop "K mul" (n 1000000) (kOf seed) (fun _ a ↦ a * b) kHex
  timeLoop "K inv" (n 100000) (kOf seed) (fun _ a ↦ (a + b)⁻¹) kHex
  let bw := xs seed
  timeLoop "K mul on words" (n 1000000) seed (fun _ a ↦ FastBF64.mulWord a bw) toString
  -- E
  let be := eOf (xs (xs (xs seed)))
  timeLoop "E add" (n 1000000) (eOf seed) (fun _ a ↦ a + be) toString
  timeLoop "E mul" (n 100000) (eOf seed) (fun _ a ↦ a * be) toString
  timeLoop "E inv" (n 1000) (eOf seed) (fun _ a ↦ (a + be)⁻¹) toString
  timeLoop "E inv (Field dictionary)" (n 1000) (eOf seed) (fun _ a ↦ fieldInv (a + be)) toString
  -- BLAKE2s
  for len in [64, 512] do
    let data ← force (bytesOf seed len)
    timeLoop s!"BLAKE2s {len} B" (n (if len = 64 then 20000 else 3000))
      (Blake2sHash.blake2sBytes data)
      (fun _ d ↦ Blake2sHash.blake2sBytes (d[0].toUInt8 :: data.tail)) (fun d ↦ toString d[0])
  -- Merkle root over 2^12 rows of 8 words
  let leaves : Vector (List K) (2 ^ 12) ← force <| Vector.ofFn fun i ↦
    (List.range 8).map fun j ↦ kOf (xs (seed + (i.val * 8 + j).toUInt64))
  timeLoop "Merkle root 2^12 rows x 8 K" (n 2) (0 : UInt32)
    (fun i acc ↦ acc ^^^ (merkleRoot (leaves.set 0 [kOf (seed + i.toUInt64)]))[0])
    toString
  -- evalMle of a 2^16 E-table at an E point
  let table : CMlPolynomialEval E 16 ← force <|
    CMlPolynomialEval.mk 16 (Vector.ofFn fun i ↦ eOf (xs (seed + i.val.toUInt64)))
  let point : Vector E 16 ← force <| Vector.ofFn fun i ↦ eOf (xs (xs (seed * 3 + i.val.toUInt64)))
  timeLoop "evalMle 2^16 E-table" (n 2) (0 : E)
    (fun i acc ↦ acc + CMlPolynomialEval.evalMle table (point.set 0 (point[0] + eOf i.toUInt64)))
    toString

end LeanerVMBench

/-- `leanervm-bench [percent]`: run every workload, iteration counts scaled to `percent` per cent
(default `100`). -/
def main (args : List String) : IO Unit := do
  let seed : UInt64 := ((← IO.getEnv "LEANERVM_BENCH_SEED").getD "12345").toNat!.toUInt64
  let percent := ((args.head?.bind String.toNat?).getD 100)
  IO.println s!"leanervm-bench: seed {seed}, {percent}% of the base iteration counts"
  LeanerVMBench.run seed percent
