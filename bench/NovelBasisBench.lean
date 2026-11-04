module

import LeanerVM.Protocol.NovelBasis
import Lean.Data.Json

/-!
# Native column-weight microbenchmark

Compare an anchored copy of the reference product with the public `Weight.mle` route.
The latter is compiled through the proved recurrence. Inputs vary by the runtime seed and
iteration. Checksums retain every output. `check` compares every full field value, independently of
checksums; `first` measures the first public-route evaluation in a fresh process. `startup`
runs only module initialization, whose external time includes the loader and module setup.
The timed intervals are local evaluator costs, not whole-verifier or Rust comparisons.
-/

open LeanerVM.Parameters LeanerVM.Protocol Lean

private def point (κ seed : ℕ) : Vector E κ := Vector.ofFn fun i ↦
  E.ofLimbs (K.ofBits (seed + i + 1)) (K.ofBits (3 * i + 5)) (K.ofBits (seed + 7))

private def reference (κ R q : ℕ) : E :=
  let v : Fin (2 ^ (κ + R)) := ⟨q % 2 ^ (κ + R), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  let r := point κ q
  ∏ k : Fin κ, ((1 - r[k]) + r[k] * (algebraMap K E) (normW k (domainPt v)))

private def route (κ R q : ℕ) : E :=
  let v : Fin (2 ^ (κ + R)) := ⟨q % 2 ^ (κ + R), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  (columnWeight (algebraMap K E) κ R v).mle (point κ q)

private def batch (f : ℕ → ℕ → ℕ → E) (κ R seed samples : ℕ) : ℕ :=
  (List.range samples).foldl (fun acc i ↦
    let v := f κ R (seed + 17 * i)
    (acc + (v.limb 0).toBitVec.toNat + 3 * (v.limb 1).toBitVec.toNat +
      7 * (v.limb 2).toBitVec.toNat) % (2 ^ 64 - 59)) 0

private def timed (f : ℕ → ℕ → ℕ → E) (κ R seed samples : ℕ) : IO (ℕ × ℕ) := do
  let start ← IO.monoNanosNow
  -- The reference allocation forces the batch before the second timer read. A pure `let`
  -- may be floated past that read by the compiler; inspect emitted C before timing.
  let result ← IO.mkRef (batch f κ R seed samples)
  let stop ← IO.monoNanosNow
  let value ← result.get
  pure (stop - start, value)

private def row (algorithm : String) (κ R seed samples ns checksum : ℕ) : Json :=
  Json.mkObj [("algorithm", toJson algorithm), ("kappa", toJson κ), ("rate", toJson R),
    ("seed", toJson seed), ("samples", toJson samples), ("elapsed_ns", toJson ns),
    ("checksum", toJson checksum)]

/-- Record all three canonical limbs, rather than treating a checksum as equality evidence. -/
private def valueJson (x : E) : Json :=
  toJson [(x.limb 0).toBitVec.toNat, (x.limb 1).toBitVec.toNat, (x.limb 2).toBitVec.toNat]

private def firstUse (κ R seed : ℕ) : IO Unit := do
  if κ > 65 || R > 2 then
    throw (IO.userError "first expects kappa <= 65 and rate <= 2")
  let start ← IO.monoNanosNow
  let result ← IO.mkRef (route κ R seed)
  let stop ← IO.monoNanosNow
  let value ← result.get
  -- Deliberately after the first-use timer: do not warm the inverse cache beforehand.
  unless value == reference κ R seed do
    throw (IO.userError "first-use full field value mismatch")
  IO.println (Json.mkObj [("mode", toJson "first-use"), ("kappa", toJson κ),
    ("rate", toJson R), ("seed", toJson seed), ("elapsed_ns", toJson (stop - start)),
    ("value", valueJson value)]).compress

private def checkValues (samples seed : ℕ) : IO Unit := do
  if samples = 0 || samples > 16 then
    throw (IO.userError "check samples must be in [1,16]")
  for κ in [0, 1, 2, 8, 22, 64, 65] do
    for i in List.range samples do
      let q := seed + 17 * i
      let actual := route κ 1 q
      unless actual == reference κ 1 q do
        throw (IO.userError "full field value mismatch")
      IO.println (Json.mkObj [("mode", toJson "full-value-check"),
        ("kappa", toJson κ), ("rate", toJson (1 : ℕ)), ("query", toJson q),
        ("value", valueJson actual)]).compress

/-- Run both algorithms on the same workload; compare outputs before interpreting timings. -/
public def main (args : List String) : IO Unit := do
  if args == ["startup"] then
    IO.println "{\"mode\":\"startup-only\"}"
    return
  if args.head? == some "first" then
    let κ := (args[1]?.bind String.toNat?).getD 22
    let R := (args[2]?.bind String.toNat?).getD 1
    let seed := (args[3]?.bind String.toNat?).getD 20261028
    firstUse κ R seed
    return
  if args.head? == some "check" then
    let samples := (args[1]?.bind String.toNat?).getD 2
    let seed := (args[2]?.bind String.toNat?).getD 20261028
    checkValues samples seed
    return
  let samples := (args[0]?.bind String.toNat?).getD 32
  let seed := (args[1]?.bind String.toNat?).getD 20261028
  if samples = 0 || samples > 10000 then
    throw (IO.userError "samples must be in [1,10000]")
  for (κ, R) in [(0, 1), (1, 1), (8, 2), (22, 1)] do
    unless batch reference κ R seed 2 == batch route κ R seed 2 do
      throw (IO.userError "warmup checksum mismatch")
    let (oldNs, oldValue) ← timed reference κ R seed samples
    let (newNs, newValue) ← timed route κ R seed samples
    unless oldValue == newValue do
      throw (IO.userError "timed checksum mismatch")
    IO.println (row "reference-product" κ R seed samples oldNs oldValue).compress
    IO.println (row "weight.mle" κ R seed samples newNs newValue).compress
