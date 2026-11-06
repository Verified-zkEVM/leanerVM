/-
  LeanerVM.Protocol.Replay

  The verifier run again on a log of the hash's answers: in a run of the random-oracle game whose
  joint log is consistent, the verifier answered from the joint log returns the game's verdict and
  asks exactly the verifier's logged queries.
-/

module

public import LeanerVM.Protocol.RandomOracleGame
public import LeanerVM.Protocol.Verify.Hom
public import LeanerVM.Protocol.ToVCVio.LogReplay

/-!
# The verifier, replayed on a log

`replay log prog input proof` runs the executable verifier with every hash answered by the log's
first answer to it (`MerkleTree.logAnswer`), its queries recorded, and fails at a hash the log
does not answer. It is the verifier on the oracle, simulated by `QueryLog.replayImpl`
(`replay_eq_simulateQ`, from `verifyWith_simulateQ`).

`replay_of_mem_support_loggedGame`: in a possible run `g` of the random-oracle game whose joint log
`g.log` is consistent, the replay on `g.log` returns the verdict `g.ok` and the verifier's log
`g.logV`. A possible run is one in the support of `loggedGame`, where a query may be answered by
anything, so the same holds of a run under the lazy random oracle or under BLAKE2s
(`QueryLog.support_simulateQ_subset`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa OracleComp OracleSpec Verify

@[expose] public section

/-- **The verifier, replayed on a log**: every hash answered by the log's first answer to it, the
queries recorded; `none` at a hash the log does not answer. -/
def replay (log : hashSpec.QueryLog) (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) : Option (Bool × hashSpec.QueryLog) :=
  (verifyWith (QueryLog.replayImpl (MerkleTree.logAnswer log)) prog input proof).run []

/-- The replay is the verifier on the oracle, simulated by the log's answers. -/
theorem replay_eq_simulateQ (log : hashSpec.QueryLog) (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) :
    replay log prog input proof =
      (simulateQ (QueryLog.replayImpl (MerkleTree.logAnswer log))
        (verifyWith hashQuery prog input proof)).run [] := by
  rw [replay, ← verifyWith_simulateQ]
  rfl

/-- A consistent log answers each of its queries as it was logged. -/
theorem logAnswer_of_consistent {log : hashSpec.QueryLog} (hc : QueryLog.Consistent log)
    {e : (_ : List UInt8) × Digest} (he : e ∈ log) : MerkleTree.logAnswer log e.1 = some e.2 := by
  rcases hfind : log.find? (fun e'' ↦ e''.1 = e.1) with _ | e'
  · have h := List.find?_eq_none.mp hfind e he
    simp at h
  have he' := List.mem_of_find?_eq_some hfind
  have hk : e'.1 = e.1 := by simpa using List.find?_some hfind
  simp only [MerkleTree.logAnswer, hfind, Option.map_some, hc e' he' e he hk]

/-- **A run of the game, replayed**: in a possible run of the random-oracle game whose joint log
is consistent, the verifier replayed on the joint log returns the run's verdict and asks the
verifier's logged queries. -/
theorem replay_of_mem_support_loggedGame {prog : Program} {input : PublicInput} {A : Adversary}
    {g : Run} (hg : g ∈ support (loggedGame verifyWith prog input A))
    (hc : QueryLog.Consistent g.log) : replay g.log prog input g.proof = some (g.ok, g.logV) := by
  simp only [loggedGame, mem_support_bind_iff, mem_support_pure_iff] at hg
  obtain ⟨⟨proof, logA⟩, -, ⟨ok, logV⟩, hV, rfl⟩ := hg
  rw [replay_eq_simulateQ]
  have h := QueryLog.run_simulateQ_replayImpl (MerkleTree.logAnswer (logA ++ logV))
    (verifyWith hashQuery prog input proof) hV
    (fun e he ↦ logAnswer_of_consistent hc (List.mem_append_right _ he)) []
  simpa [Run.log] using h

end

end LeanerVM.Protocol
