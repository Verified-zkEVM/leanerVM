/-
  LeanerVMVerify

  The executable verifier on the Rust proof fixture, compiled into the `leanervm-verify`
  executable: the verdict, every mutation's outcome, WHIR's algebra on the honest transcript,
  and the time of a run.
-/

import LeanerVM.Protocol.Verify
import LeanerVMTests.Protocol.Verify

/-!
# The `leanervm-verify` executable

Runs, compiled, what `tests/LeanerVMTests/Protocol/Verify.lean` cannot afford to interpret: `verify`
on the proof of `tests/LeanerVMTests/Protocol/RustProofData.lean` (`scripts/dump-proof-rust.sh`),
on each of its `mutations` and, for the fixture, its `statementMutations`, with the stage
`outcomeOf` names for the rejection, then `whirChecks`. It prints one line per check, then times
`verify` on the honest proof the number of times given by the first argument (default `1`), the
fixture's parsing excluded. With a second argument, a file in the same dump format (a test vector
of `tests/vectors/`, written by `leanervm-prove`), it checks that proof and its mutations
(`mutationsOf`) instead. The exit code is `1` if any check fails.
-/

open LeanerVM.Protocol LeanerVM.Protocol.Verify LeanerVMTests.Protocol.RustProof
open LeanerVMTests.Protocol.Verify

/-- Return a value through an opaque call, so that its computation stays inside the timed
interval. -/
@[noinline] def forceVerdict (f : Fixture) : IO Bool :=
  pure (verify f.prog f.input f.proof)

/-- `leanervm-verify [runs] [file]`: check the honest proof and its mutations, then time `runs`
runs of `verify` (default `1`); the Rust fixture's proof, or the proof of `file`. -/
def main (args : List String) : IO UInt32 := do
  let runs := (args.head?.bind String.toNat?).getD 1
  let vector := args[1]?
  let loaded ← match vector with
    | none => pure (some fx)
    | some file => return load (← IO.FS.readFile file)
  let some f := loaded | do
    IO.println s!"FAIL the loader rejects {vector.getD ""}"
    return 1
  IO.println s!"leanervm-verify: {f.proof.stream.length} scalars, {f.proof.merkle.length} openings"
  let mut failed := 0
  let honest := verify f.prog f.input f.proof
  IO.println s!"honest proof: verify = {honest}"
  unless honest do failed := failed + 1
  for m in mutationsOf f do
    let p := m.change f.proof
    let v := verify f.prog f.input p
    let o := outcomeOf f p
    let ok := !v && o == m.expected
    unless ok do failed := failed + 1
    let stage := ((reprStr o).replace "LeanerVMTests.Protocol.Verify.Outcome." "").replace
      "LeanerVM.Protocol.ReadError." ""
    IO.println s!"{if ok then "ok  " else "FAIL"} {m.name}: verify = {v}, rejected at {stage}"
  if vector.isNone then
    for m in statementMutations do
      let v := verify m.prog m.input f.proof
      let o := outcomeAt m.prog m.input f.proof
      let ok := !v && o == m.expected
      unless ok do failed := failed + 1
      let stage := ((reprStr o).replace "LeanerVMTests.Protocol.Verify.Outcome." "").replace
        "LeanerVM.Protocol.ReadError." ""
      IO.println s!"{if ok then "ok  " else "FAIL"} the statement, {m.name}: verify = {v}, \
        rejected at {stage}"
    let w := whirChecks (whirMutations.map (·.1))
    let wOk := w == whirMutations.map (·.2)
    unless wOk do failed := failed + 1
    IO.println s!"{if wOk then "ok  " else "FAIL"} WHIR's algebra on the honest transcript: {w}"
  for i in [0:runs] do
    let t0 ← IO.monoNanosNow
    let ok ← forceVerdict f
    let t1 ← IO.monoNanosNow
    IO.println s!"run {i}: verify = {ok} in {(t1 - t0).toFloat / 1e6} ms"
  IO.println s!"{failed} failed"
  return if failed = 0 then 0 else 1
