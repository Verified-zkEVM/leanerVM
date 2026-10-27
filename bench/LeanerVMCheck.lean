/-
  LeanerVMCheck

  The executable verifier on proof files, one verdict per file, compiled into the
  `leanervm-check` executable: the Lean side of the differential test against the Rust verifier.
-/

import LeanerVM.Protocol.Verify
import LeanerVMTests.Protocol.Verify

/-!
# The `leanervm-check` executable

Reads proofs in the dump format of `scripts/dump-proof-rust.sh` and prints, per file, one line
`<file>\t<verdict>\t<stage>\t<microseconds>`. The verdict is `ACCEPT` or `REJECT` (`verify`'s
answer) or `PARSEFAIL` (the loader rejects the file). The stage is the one `outcomeAt` names,
followed by `;hashmismatch` when the file's program hash is not the program's (`verify` does not
read it); `INCONSISTENT` replaces the verdict when `verify` and `outcomeAt` disagree. With `serve` as the first argument it reads the paths
from standard input, one per line, flushing after each verdict; otherwise the arguments are the
paths.
-/

open LeanerVM.Protocol LeanerVM.Protocol.Verify LeanerVMTests.Protocol.RustProof
open LeanerVMTests.Protocol.Verify

/-- The verdict line of one file. -/
def checkFile (file : String) : IO String := do
  let text ← try IO.FS.readFile file catch _ => pure ""
  let t0 ← IO.monoNanosNow
  let some f := load text | return s!"{file}\tPARSEFAIL\t-\t0"
  let note := if (programHash f.prog).toList != f.programHash.toList then ";hashmismatch" else ""
  let v := verify f.prog f.input f.proof
  let o := outcomeAt f.prog f.input f.proof
  let t1 ← IO.monoNanosNow
  let stage := ((reprStr o).replace "LeanerVMTests.Protocol.Verify.Outcome." "").replace
    "LeanerVM.Protocol.ReadError." ""
  let verdict :=
    if v != (o == .accepted) then "INCONSISTENT" else if v then "ACCEPT" else "REJECT"
  return s!"{file}\t{verdict}\t{stage}{note}\t{(t1 - t0) / 1000}"

/-- `leanervm-check <file>...` or `leanervm-check serve`. -/
def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  if args.head? == some "serve" then
    let inp ← IO.getStdin
    repeat
      let line ← inp.getLine
      if line.isEmpty then break
      let file := line.trimAsciiEnd.toString
      unless file.isEmpty do
        out.putStrLn (← checkFile file)
        out.flush
  else
    for file in args do
      out.putStrLn (← checkFile file)
      out.flush
  return 0
