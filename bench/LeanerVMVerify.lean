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
on each of its `mutations`, with the stage `outcome` names for the rejection, then `whirChecks`
and `bytecodeAgrees`. It prints one line per check, then times `verify` on the honest proof the
number of times given by the first argument (default `1`), the fixture's parsing excluded. The
exit code is `1` if any check fails.
-/

open LeanerVM.Protocol LeanerVM.Protocol.Verify LeanerVMTests.Protocol.RustProof
open LeanerVMTests.Protocol.Verify

/-- Return a value through an opaque call, so that its computation stays inside the timed
interval. -/
@[noinline] def forceVerdict (f : Fixture) : IO Bool :=
  pure (verify f.prog f.input f.proof)

/-- `leanervm-verify [runs]`: check the honest proof and its mutations, then time `runs` runs of
`verify` (default `1`). -/
def main (args : List String) : IO UInt32 := do
  let runs := (args.head?.bind String.toNat?).getD 1
  let f ← IO.lazyPure fun _ ↦ fx
  IO.println s!"leanervm-verify: {f.proof.stream.length} scalars, {f.proof.merkle.length} openings"
  let mut failed := 0
  let honest := verify f.prog f.input f.proof
  IO.println s!"honest proof: verify = {honest}"
  unless honest do failed := failed + 1
  for m in mutations do
    let p := m.change f.proof
    let v := verify f.prog f.input p
    let o := outcome p
    let ok := !v && o == m.expected
    unless ok do failed := failed + 1
    let stage := ((reprStr o).replace "LeanerVMTests.Protocol.Verify.Outcome." "").replace
      "LeanerVM.Protocol.ReadError." ""
    IO.println s!"{if ok then "ok  " else "FAIL"} {m.name}: verify = {v}, rejected at {stage}"
  let w := whirChecks (whirMutations.map (·.1))
  let wOk := w == whirMutations.map (·.2)
  unless wOk do failed := failed + 1
  IO.println s!"{if wOk then "ok  " else "FAIL"} WHIR's algebra on the honest transcript: {w}"
  let b := bytecodeAgrees
  unless b do failed := failed + 1
  IO.println s!"{if b then "ok  " else "FAIL"} the bytecode multilinear is the program's share"
  for i in [0:runs] do
    let t0 ← IO.monoNanosNow
    let ok ← forceVerdict f
    let t1 ← IO.monoNanosNow
    IO.println s!"run {i}: verify = {ok} in {(t1 - t0).toFloat / 1e6} ms"
  IO.println s!"{failed} failed"
  return if failed = 0 then 0 else 1
