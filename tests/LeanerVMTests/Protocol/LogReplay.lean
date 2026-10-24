import LeanerVM.Protocol.Replay

/-!
# Replaying a logged run

`QueryLog.replayImpl ans` on a computation of two queries, the second depending on the first's
answer: answered by a total `ans`, the replay returns the value and records both queries in order;
a query `ans` does not answer makes the replay fail. `MerkleTree.logAnswer` takes a log's first
answer to a query, so a log that asks a query twice with two answers replays at the first: an
inconsistent log is not the trace of one function, which `logAnswer_of_consistent` excludes.
-/

namespace LeanerVMTests.Protocol.LogReplay

open OracleComp OracleSpec LeanerVM.Protocol

/-- Two queries, the second asked at the first's answer plus one. -/
def twoQueries : OracleComp (ℕ →ₒ ℕ) ℕ := do
  let a ← liftM ((ℕ →ₒ ℕ).query 1)
  let b ← liftM ((ℕ →ₒ ℕ).query (a + 1))
  return a + b

/-- The replay of `twoQueries` answered by `ans`. -/
def replayed (ans : ℕ → Option ℕ) : Option (ℕ × (ℕ →ₒ ℕ).QueryLog) :=
  (simulateQ (QueryLog.replayImpl ans) twoQueries).run []

#guard replayed (fun n ↦ some (10 * n)) == some (120, [⟨1, 10⟩, ⟨11, 110⟩])
-- The second query is not answered.
#guard replayed (fun n ↦ if n = 1 then some 10 else none) == none
-- Answers from a log: the second query is the first answer plus one.
#guard replayed (MerkleTree.logAnswer [⟨1, 4⟩, ⟨5, 7⟩]) == some (11, [⟨1, 4⟩, ⟨5, 7⟩])
-- A log asking `1` twice replays at its first answer.
#guard replayed (MerkleTree.logAnswer [⟨1, 4⟩, ⟨1, 9⟩, ⟨5, 7⟩, ⟨10, 0⟩]) ==
  some (11, [⟨1, 4⟩, ⟨5, 7⟩])

end LeanerVMTests.Protocol.LogReplay
