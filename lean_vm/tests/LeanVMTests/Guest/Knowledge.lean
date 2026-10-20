import LeanVM.Guest.EndKnow

/-!
# Tests: the guest's soundness, its witness named

* The end theorems rest on Lean's three standard axioms only.
* The decoder reads the seed and the statement off `main`'s frame, by definition.
* The named form implies the existential one (`GuestSound`'s conclusion, at the input's digest).
* Why the existential one says little: the empty statement holds under any seed and any deferred
  values (`NodeSpec` of a statement with no claims, no children and the points at zero), so a
  digest of it exists for almost every public input.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Check LeanVM.Guest.End LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier

/-- info: 'LeanVM.Guest.End.guest_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_knowledge

/-- info: 'LeanVM.Guest.End.aggregate_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_knowledge

/-- info: 'LeanVM.Guest.End.aggregate_sound_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound_outer

/-- info: 'LeanVM.Guest.End.decode_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.decode_binds

/-! ## The decoder reads `main`'s frame -/

example {κ : ℕ} (L : MemImage κ) : (decode L).seed = B1.Main.decSeed (valG L 1 (certOf 1)) := rfl

example {κ : ℕ} (L : MemImage κ) :
    (decode L).statement = B1.Main.decStmt (valG L 1 (certOf 1)) L.read := rfl

/-! ## The named form implies the existential one -/

example (input : PublicInput) (t : Trace guest) (hv : ValidExecution guest input t) :
    ∃ seed s, statementDigest seed s = publicDigest input ∧ s.defer.Shaped bytecode ∧
      NodeSpec bytecode seed s := by
  obtain ⟨hd, hrel⟩ := guest_knowledge input t hv
  exact ⟨_, _, hd, hrel.1, _, hrel⟩

/-! ## The existential one is nearly vacuous -/

/-- The statement with no claims and its deferred claim at the zero points, values `v a b`. -/
def emptyStatement (v a b : E) : NodeStatement :=
  ⟨⟨[], [], []⟩, ⟨List.replicate 22 0, v, List.replicate (2 * blake2sR1csLogSize) 0, a, b⟩⟩

/-- `NodeSpec` holds of the empty statement, whatever the seed and the deferred values: its digest
ranges over a seed and three field elements, so almost every public input is one's. -/
example (seed : Digest) (v a b : E) (hints : BatchHints) :
    NodeSpec bytecode seed (emptyStatement v a b) := by
  have hlog : Nat.log2 bytecode.length = 22 := by rw [bytecode_length, Nat.log2_two_pow]
  refine ⟨⟨[], [], [], [], hints⟩, ⟨?_, by simp, by simp [emptyStatement], by simp [emptyStatement],
    by simp [emptyStatement], ?_⟩⟩
  · simp [emptyStatement, DeferredClaim.Shaped, hlog]
  · simp [emptyStatement, DeferredClaim.AtZero, hlog]
