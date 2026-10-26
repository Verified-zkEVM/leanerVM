import LeanDa.RpmCodeBinding
import PqDas.Target.Scheme
import LeanDa.Defs

/-!
# Completeness in the random-permutation model

LeanDA is perfectly complete for every permutation `π` of the Keccak state (indeed every function):
with the hash Keccak-256 over `π` (`keccakWith π`) and the membership challenges the deployed
duplex over `π`, every position of every message's honest commitment opens and verifies
(`leanDa_perfectlyComplete_rpm : PerfectlyCompleteRpm`).

The proof is a transfer of Benedikt Wagner's completeness proof (`PqDas.scheme_perfectlyComplete`).
For a fixed `π` the experiment flips no coin but the argument's setup: the verifier's programs,
over `Id`, are their pure counterparts (`membershipChallengesM_id`, `verifyCellM_id`), so the
committer and the verifier compute the same challenges, and the verdict is the honest run's for
those challenges. Wagner's proof shows that the
honest run verifies for every challenge (`PqDas.honest_verify`, the core of his proof), from the
completeness of the Merkle commitment (`merkleVC_perfectlyComplete`), of the membership test
(`checker_complete`) and of the argument.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common PqDas
open scoped ENNReal

namespace LeanDa

/-! ## Completeness -/

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation**
(Benedikt Wagner's completeness, transferred). For a fixed `π` the verifier's programs, over `Id`,
are the scheme's pure ones (`membershipChallengesM_id`, `verifyCellM_id`), so the committer and
the verifier draw the same challenges, and the experiment is the argument's setup followed by the
honest run for those challenges, which verifies for every challenge (`PqDas.honest_verify`). -/
theorem leanDa_perfectlyComplete_rpm : PerfectlyCompleteRpm := by
  intro r π Crs Proof ps hps msg p
  rw [OracleComp.prEvent_eq_one_iff]
  intro b hb
  simp only [completenessExpRpm, support_bind, Set.mem_iUnion, support_pure,
    Set.mem_singleton_iff, exists_prop] at hb
  obtain ⟨crs, hcrs, rfl⟩ := hb
  have h := honest_verify (code r) (merkleVC r (keccakWith π)) (checker r) ps
    (merkleVC_perfectlyComplete r _) (checker_complete r) hps (ckVC := ()) (by simp [merkleVC])
    hcrs msg p (toChallenges (membershipChallenges (keccakWith π) π
      (commitCells (keccakWith π) ((code r).encode msg))))
  simp only [merkleVC, ← verifyCellM_id] at h
  exact h

end LeanDa
