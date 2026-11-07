/-
  LeanVM.Wire.Complete

  Completeness on the wire: the honest prover's bytes are accepted by the verifier on bytes with
  the structured bound `2^-256` (`LeanVM.CompletenessOnBytes`).
-/

import LeanVM.Prover.End
import LeanVM.Protocol.ExperimentBridge
import LeanVM.Wire.Model

/-!
# Completeness on the wire

The experiment on the wire (`completenessExperimentOnBytes`) runs the honest prover, encodes its
proof (`Proof.toBytes`), decodes the bytes (`Proof.fromBytes`) and verifies the result, all over
the lazily sampled permutation. Its verdict is the structured experiment's
(`completenessExperiment`), so `CompletenessOnBytes` holds with the same bound `2^-256`:

1. it is the experiment with the two calls (`completenessExperimentOnBytes_eq`), as the structured
   one is (`verifierCompletenessExperiment_eq_withHash`), decoding with the hash call
   (`fromBytes_eq_withHash`, `simulateQ_fromBytesWithHash`);
2. on every outcome of the prover's run, decoding its proof's bytes returns the proof and leaves
   the permutation as it was (`fromBytesWithHash_run_of`, `LeanVM/Wire/Model.lean`), given that
   the honest prover's proofs survive their encoding and that it hashed every input their paths
   climb through (`HonestWireFacts`, track wcparams);
3. so the experiment on the wire is the structured one with the two calls
   (`completenessExperimentOnBytes_eq_withHash`), whose rejection probability is at most
   `2^-256` (`completenessWithHash_holds`).

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open Common (queryPermutation runWithRandomPermutation)

/-- **What completeness on the wire needs of the honest prover** (track wcparams,
`LeanVM/Wire/Honest.lean`): its proofs survive their encoding with the hash they are computed
with, and it hashes every input their paths climb through. -/
def HonestWireFacts : Prop :=
  (∀ (h : Bytes → Digest) (F : KeccakState → KeccakState) (prog : LeanIsaProgram)
      (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) (p : Proof),
      Prover.proveWithHash (m := Id) h F prog input t ρ fuel = some p → WireDecodable h p) ∧
    ∀ (h : Bytes → Digest) (F : KeccakState → KeccakState) (prog : LeanIsaProgram)
      (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) (p : Proof) (log : List Bytes),
      (Prover.proveWithHash (loggedHash h) (loggedPerm F) prog input t ρ fuel).run [] =
          (some p, log) → ClimbInputsIn h p log

/-- The structured verdict on the decoded proof, after the honest prover with the two calls. -/
noncomputable def completenessExperimentOnBytesWithHash (prog : LeanIsaProgram)
    (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) : ProbComp Bool :=
  (simulateQ keccakCallsOverRandomPermutation (do
    match ← proverWithHash prog input t ρ fuel with
    | none => pure false
    | some p => do
      match ← fromBytesWithHash callKeccak256 p.toBytes with
      | none => pure false
      | some q => verifierWithHash callKeccak256 callKeccakF1600 prog input q)).run' []

/-- **The experiment on the wire is the one with the two calls.** -/
theorem completenessExperimentOnBytes_eq (prog : LeanIsaProgram) (input : PublicInput)
    (t : Execution prog) (ρ fuel : ℕ) :
    completenessExperimentOnBytes prog input t ρ fuel =
      completenessExperimentOnBytesWithHash prog input t ρ fuel := by
  have hD : ∀ bytes : Bytes, Proof.fromBytes queryPermutation bytes =
      simulateQ keccakCallsOverQueryPermutation (fromBytesWithHash callKeccak256 bytes) := by
    intro bytes
    rw [fromBytes_eq_withHash, simulateQ_fromBytesWithHash]
    rfl
  have hin : (do
      match ← leanVmHonestProverOnBytes queryPermutation prog input t ρ fuel with
      | none => pure false
      | some bytes => leanVmVerifierOnBytes queryPermutation prog input bytes :
        OracleComp Common.RandomPermutationOracles Bool) =
      simulateQ keccakCallsOverQueryPermutation (do
        match ← proverWithHash prog input t ρ fuel with
        | none => pure false
        | some p => do
          match ← fromBytesWithHash callKeccak256 p.toBytes with
          | none => pure false
          | some q => verifierWithHash callKeccak256 callKeccakF1600 prog input q) := by
    simp only [leanVmHonestProverOnBytes, leanVmVerifierOnBytes, prover_queryPermutation, hD,
      verifier_queryPermutation, simulateQ_bind, bind_assoc, pure_bind]
    congr 1
    funext o
    cases o with
    | none => simp
    | some p =>
      simp only [Option.map_some, simulateQ_bind]
      congr 1
      funext r
      cases r <;> simp
  rw [completenessExperimentOnBytes, runWithRandomPermutation, hin,
    simulateQ_lazy_keccakCallsOverQueryPermutation]
  rfl

/-- **On the wire, the verdict is the structured one**, for the honest prover with the two
calls: decoding its proof's bytes returns the proof and adds no edge (`fromBytesWithHash_run_of`).
-/
theorem completenessExperimentOnBytesWithHash_eq (hf : HonestWireFacts) (prog : LeanIsaProgram)
    (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) :
    completenessExperimentOnBytesWithHash prog input t ρ fuel =
      verifierCompletenessExperimentWithHash proverWithHash prog input t ρ fuel := by
  unfold completenessExperimentOnBytesWithHash verifierCompletenessExperimentWithHash
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine bind_congr_of_forall_mem_support _ fun z hz ↦ ?_
  rcases z with ⟨o, s⟩
  cases o with
  | none => rfl
  | some p =>
    have hrun := fromBytesWithHash_run_of (proverWithHash prog input t ρ fuel)
      (fun h F p hp ↦ hf.1 h F prog input t ρ fuel p (by
        rwa [proverWithHash, simulateQ_proveWithHash] at hp))
      (fun h F p log hp ↦ hf.2 h F prog input t ρ fuel p log (by
        rwa [proverWithHash, simulateQ_proveWithHash] at hp))
      hz
    simp only [simulateQ_bind, StateT.run_bind, hrun, pure_bind]

/-- **Completeness on the wire**, from what it needs of the honest prover. -/
theorem completenessOnBytes_of (hf : HonestWireFacts) : CompletenessOnBytes := by
  intro prog input t ρ hv hs hρ
  rw [completenessExperimentOnBytes_eq, completenessExperimentOnBytesWithHash_eq hf]
  exact completenessWithHash_holds prog input t ρ hv hs hρ

end LeanVM.Wire
