import LeanVM.E2E.Statement

/-!
# Tests: partial words (decision E2E-10)

* A hole at the root makes the root the hole's digest; a hole at an inner node stands for its
  subtree; a full word's partial root is the deployed Merkle root.
* Presence: the rows under a hole are absent, the others present.
* A full word's candidates, and the candidates V_I follows on it, are today's.
-/

namespace LeanVMTests.E2E.PartialWord

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash
open LeanVM.E2E

variable (H : Bytes → Digest) (W : Word) (d : Digest)

/-- A tree of height `2` with a hole over the left half (node `0` of level `1`). -/
def leftHole : PWord := ⟨W, fun k j ↦ if k = 1 ∧ j = 0 then some d else none⟩

/-- A hole at the root is the root. -/
example : pTreeRootM (m := Id) (fun x ↦ pure (H x)) 2
    ⟨W, fun k j ↦ if k = 2 ∧ j = 0 then some d else none⟩ = d := rfl

/-- A hole stands for its subtree: the root hashes the hole's digest with the right subtree. -/
example : pTreeRootM (m := Id) (fun x ↦ pure (H x)) 2 (leftHole W d) =
    H (digestBytes d ++ digestBytes (H (digestBytes (H ((W 2).flatMap kBytes)) ++
      digestBytes (H ((W 3).flatMap kBytes))))) := rfl

/-- The rows under the hole are absent, the others present. -/
example : ¬ (leftHole W d).Present 2 1 ∧ (leftHole W d).Present 2 2 := by
  refine ⟨fun h ↦ ?_, fun k hk ↦ ?_⟩
  · have := h 1 (by omega)
    simp [leftHole] at this
  · simp only [leftHole]
    interval_cases k <;> simp

/-- A full word's partial root is the deployed root. -/
example (ht : ℕ) : pTreeRootM (m := Id) (fun x ↦ pure (H x)) ht (PWord.full W) =
    treeRoot H ht W :=
  pTreeRootM_full H ht W

/-- A full word's candidates V_I follows are today's. -/
example (prog : Program) (s : LeanIsa.Sizes) (ρ ht : ℕ) (pi : Digest) :
    blindCandidatesS prog s ρ ht pi (PWord.full W) = blindCandidates prog s ρ pi W :=
  blindCandidatesS_full prog s ρ ht pi W

end LeanVMTests.E2E.PartialWord
