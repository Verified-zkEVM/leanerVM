import LeanerVM.Protocol.VerifierQueries
import LeanerVM.Protocol.Replay
import LeanerVM.Protocol.LeanVmReader
import LeanerVMTests.Protocol.RustProof

/-!
# The verifier's queries on the Rust proof

The executable verifier on the fixture's Rust proof, every hash counted, accepts after 3936
hashes: the chain walk's 1004 and the openings' 2932. The bound at the fixture's sizes and rate,
`queryCountAt`, is 6162: the chain's count exactly and, for the openings, a query per stored row
and per row and level of the tree, where the pruned openings share their upper nodes.

The verifier replayed on its own log of hashes (`replay`) accepts and records that log, query for
query; with an early answer erased it fails at the query it no longer answers. The bound whatever
the program and the input, `verifierQueriesBound`, is 13697. The checks share one run of the
interpreted verifier and two replays.
-/

namespace LeanerVMTests.Protocol.VerifierQueries

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash LeanerVM.Protocol.Verify
open LeanerVMTests.Protocol.RustProof

/-- The fixture's verdict and the log of its hashes, in order. -/
def verifierLog : Bool × hashSpec.QueryLog :=
  let (ok, rev) := (verifyWith (m := StateM hashSpec.QueryLog)
    (fun t ↦ do let d := blake2sBytes t; modify (⟨t, d⟩ :: ·); pure d) fx.prog fx.input
    fx.proof).run []
  (ok, rev.reverse)

-- The verifier accepts after 3936 hashes, within the bound at the fixture's sizes; replayed on its
-- own log it accepts and records that log; with an early answer erased, the replay stops at the
-- query it no longer answers. One run of the verifier and two replays.
#guard
  let (ok, log) := verifierLog
  ok && log.length == 3936 &&
    decide (log.length ≤ VerifierQueries.queryCountAt fx.prog fx.input sizes.1 sizes.2) &&
    replay log fx.prog fx.input fx.proof == some (true, log) &&
    replay (log.eraseIdx 20) fx.prog fx.input fx.proof == none

-- The bound whatever the program and the input, above the fixture's bound at its sizes.
#guard LeanVmReader.verifierQueriesBound == 13697 &&
  VerifierQueries.queryCountAt fx.prog fx.input sizes.1 sizes.2 ≤ LeanVmReader.verifierQueriesBound

end LeanerVMTests.Protocol.VerifierQueries
