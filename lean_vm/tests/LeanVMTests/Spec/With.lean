import LeanVM.Spec.IsaWith
import LeanVM.Spec.NodeWith
import LeanVM.Guest.Value.HashModel
import LeanVM.Spec.Ideal.Table

/-!
# Tests: the hash-generic specification

* The bridges to the deployed definitions rest on Lean's three axioms.
* **The condition doing the work.** The Flock-blind semantics accepts a `BLAKE2S` row the
  compression function rejects: the all-zero row (zero output of zero cells under the zero
  chaining value); every deployed execution is a Flock-blind one
  (`validExecutionB_blakeFree_of_valid`, tests of `Guest/OracleModel.lean`).
* The deployed hash model is inhabited (`HashModel.deployed`).
-/

namespace LeanVMTests.Spec.With

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Guest.Value

/-- info: 'LeanVM.Semantics.validExecutionB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Semantics.validExecutionB_deployed

/-- info: 'LeanVM.Node.batchWith_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Node.batchWith_id

/-- info: 'LeanVM.Da.commitCodewordsWith_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Da.commitCodewordsWith_id

/-- The all-zero row is canonical. -/
example : blakeFree.check ![0, 0, 0, 0] 0 0 0 0 0 := by
  show CanonicalCells ![0, 0, 0, 0] 0 0 0 0 0
  decide

/-- The compression function rejects it: the zero block under the zero chaining value does not
compress to zero. -/
example : ¬ blakeDeployed.check ![0, 0, 0, 0] 0 0 0 0 0 := by
  show ¬ CompressCells ![0, 0, 0, 0] 0 0 0 0 0
  decide +kernel

/-- The deployed hash model answers BLAKE2s. -/
example (x : List UInt8) : HashModel.deployed.H x = some (LeanVM.Protocol.Blake2sHash.blake2sBytes x) := rfl

end LeanVMTests.Spec.With

namespace LeanVMTests.Spec.With.Table

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Blake2sHash

/-- The one row of the empty string's chain, its output `out`. -/
def emptyRow (out : E × E) : BlakeRow :=
  ⟨![0, 0, 0, 0], ivCells.1, ivCells.2, out.1, out.2, metadataCell 0 true⟩

theorem ivCells_cv : cellWords ivCells.1 ++ cellWords ivCells.2 = paramIv := by decide +kernel

theorem zero_words : messageWords ![0, 0, 0, 0] = blockWords [] := by decide +kernel

theorem empty_md : unpackMetadata (metadataCell 0 true) = ((0 : ℕ).toUInt64, lastBlock, 0) := by
  decide +kernel

/-- It is the standard chain of the empty string. -/
theorem stdChain_empty (out : E × E) : StdChain [] [emptyRow out] := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i hi
    obtain rfl : i = 0 := by simpa using hi
    exact ivCells_cv
  · intro i hi
    simp at hi
  · intro _
    exact ⟨zero_words, empty_md⟩

/-- **A wrong output violates the table check** at BLAKE2s. -/
example : ¬ TableOK (fun x ↦ some (blake2sBytes x)) [emptyRow (0, 0)] := by
  intro h
  have := h [] [emptyRow (0, 0)] (by decide) (by simp) (stdChain_empty _)
  revert this
  decide +kernel

/-- The true output satisfies it on this chain. -/
example : (fun x ↦ some (blake2sBytes x)) [] =
    some ((emptyRow (digestScalars (blake2sBytes []))).out) := by
  decide +kernel

end LeanVMTests.Spec.With.Table
