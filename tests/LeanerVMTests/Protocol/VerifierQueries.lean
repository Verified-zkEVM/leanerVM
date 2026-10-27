import LeanerVM.Protocol.VerifierQueries
import LeanerVM.Protocol.ChainLog
import LeanerVM.Protocol.LeanVmReader
import LeanerVMTests.Protocol.RustProof

/-!
# The verifier's queries on the Rust proof

The executable verifier on the fixture's Rust proof, every hash counted, accepts after 3936
hashes: the chain walk's 1004 and the openings' 2932. The bound at the fixture's sizes and rate,
`queryCountAt`, is 6162: the chain's count exactly and, for the openings, a query per stored row
and per row and level of the tree, where the pruned openings share their upper nodes.

The verifier's chain walk replayed on the verifier's log of hashes (`ChainLog.runReplay`) succeeds
and records the log's first 1004 queries, query for query; the whole verifier replayed on a log
with an early answer erased (`replay`) fails at the query it no longer answers. The whole replay
on the verifier's own log is not run: it repeats the verifier's algebra, and
`replay_of_mem_support_loggedGame` settles it. The bound whatever the program and the input,
`verifierQueriesBound`, is 13697. The checks share one run of the interpreted verifier.

The seed's hashes, logged, are three, in order: the program's bytes, the seed's preimage and the
first state's input; their state is the statement's seed. From the seed's hashes as queries the
verifier asks at most three queries more than `verifierQueries` (an `example`).
-/

namespace LeanerVMTests.Protocol.VerifierQueries

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.Verify
open LeanerVMTests.Protocol.RustProof

/-- The fixture's verdict and the log of its hashes, in order. -/
def verifierLog : Bool × hashSpec.QueryLog :=
  let (ok, rev) := (verifyWith (m := StateM hashSpec.QueryLog)
    (fun t ↦ do let d := blake2sBytes t; modify (⟨t, d⟩ :: ·); pure d) fx.prog fx.input
    fx.proof).run []
  (ok, rev.reverse)

/-- The queries the chain walk, replayed on a log, records, if it succeeds. -/
def chainReplay (log : hashSpec.QueryLog) : Option hashSpec.QueryLog :=
  match ChainLog.runReplay (walkChain (readerOps (QueryLog.replayImpl (MerkleTree.logAnswer log)))
      fx.prog sizes.1 fx.input
      (levelShapes (stackMu fx.prog sizes.1) ((ladderOf fx.prog sizes.1 sizes.2).getD [])))
      ⟨FsState.seed fx.prog fx.input, fx.proof.stream, fx.proof.merkle⟩ [] with
  | some (.ok _, l) => some l
  | _ => none

-- The verifier accepts after 3936 hashes, within the bound at the fixture's sizes, which is within
-- the bound whatever the program and the input; its chain walk replayed on its log records the
-- log's first 1004 queries; with an early answer erased, the replay stops at the query it no
-- longer answers. One run of the verifier.
#guard
  let (ok, log) := verifierLog
  let q := VerifierQueries.queryCountAt fx.prog fx.input sizes.1 sizes.2
  ok && log.length == 3936 && decide (log.length ≤ q) &&
    LeanVmReader.verifierQueriesBound == 13697 && decide (q ≤ LeanVmReader.verifierQueriesBound) &&
    chainReplay log == some (log.take 1004) &&
    replay (log.eraseIdx 20) fx.prog fx.input fx.proof == none

/-- The seed's state and the log of its hashes, in order. -/
def seedLog : FsState × hashSpec.QueryLog :=
  let (fs, rev) := (FsState.seedWith (m := StateM hashSpec.QueryLog)
    (fun t ↦ do let d := blake2sBytes t; modify (⟨t, d⟩ :: ·); pure d) fx.prog fx.input).run []
  (fs, rev.reverse)

#guard seedLog.1.cv == (FsState.seed fx.prog fx.input).cv &&
  seedLog.2.map (·.1) ==
    [programBytes fx.prog, seedPreimage fx.prog, seedInput (fsSeed fx.prog) fx.input]

example (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths) :
    OracleComp.IsTotalQueryBound
      (verifyFrom hashQuery (FsState.seedWith hashQuery prog input) prog input proof)
      (3 + VerifierQueries.verifierQueries prog input) :=
  VerifierQueries.verifierQueries_bound_from (VerifierQueries.isTotalQueryBound_seedWith prog input)
    prog input proof

end LeanerVMTests.Protocol.VerifierQueries
