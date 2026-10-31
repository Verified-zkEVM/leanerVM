/-
  LeanVM.Prover.Complete

  The completeness end statements for any honest prover that is the specification's honest
  prover at some witness: `LeanVM.Completeness` and `LeanVM.Guest.Budget.GuestChildComplete` with
  that prover.
-/

import LeanVM.Protocol.LeanVMRpm
import LeanVM.Guest.Child.NZRpm
import LeanVM.Guest.Child.Deployed
import LeanVM.Protocol.WithHash
import LeanVM.Guest.WithHash

/-!
# Completeness for a prover that is the specification at a witness

The completeness theorems (`LeanVM.completeness_holds`, `LeanVM.Guest.Budget.guest_child_complete`)
are proved for provers that choose a witness classically (`honestComp`, `childComp`). Their
proofs need of the prover only that, on the executions they speak of, it is the specification's
honest prover (`Rom.honestComp` at leanVM's seed and program, with the strategy
`leanVmProver prog s ρ (stackOf prog s w)`) at some witness `w` at sizes `s` that is honest
(`HonestFor`), or a child's (`ChildFor`). Here they are restated for any such prover `A`:

* `completeness_of_spec`: if on every valid execution within the cap, at a valid rate, `A` is the
  specification at an honest witness, then the body of `LeanVM.Completeness` holds for `A`, with
  the same bound `2^-256` (`completenessRpm_at`, `completenessRpm_le`);
* `guestChildComplete_of_spec`: if moreover the witness is a child's, and everywhere `A` is the
  specification at a child's witness or the empty proof (`ChildSpec`), then both parts of
  `LeanVM.Guest.Budget.GuestChildComplete` hold for `A`, with the same bound `2^-126`
  (`rpmChild_at`, `rpmChild_le`, `childOk_of_verifierRZ_of`).

The classical provers are instances (`specOnValid_honestComp`, `specOnValid_childProver`).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakHash LeanVM.Guest.Child LeanVM.Node
open OracleComp OracleSpec
open Air.Flat (EnsembleWitness)
open scoped ENNReal

/-- **The prover is the specification at an honest witness** on every valid execution within the
verifier's cap, at a valid rate. -/
def SpecOnValid (A : HonestProverWithHash)
    (W : (prog : Program) → PublicInput → Execution prog → ℕ →
      EnsembleWitness (leanIsaEnsemble prog) → Sizes → Prop) : Prop :=
  ∀ (prog : Program) (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ),
    ValidExecution prog input t → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
    ∃ w s, W prog input t ρ w s ∧
      A prog input t ρ fuel = Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
        (leanVmProgram (bytecodeWords prog) (publicDigest input))
        (leanVmProver prog s ρ (stackOf prog s w)) fuel

/-- **Completeness for a prover that is the specification at an honest witness**: the body of
`LeanVM.Completeness` for `A`. -/
theorem completeness_of_spec (A : HonestProverWithHash) (hA : SpecOnValid A HonestFor) :
    ∀ (prog : Program) (input : PublicInput) (t : Execution prog) (ρ : ℕ),
      ValidExecution prog input t → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
      Pr{let v ← verifierCompletenessExperimentWithHash A prog input t ρ (2 ^ 25)}[v = false] ≤
        (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  intro prog input t ρ hv hbudget hρ
  obtain ⟨w, s, hw, hAw⟩ := hA prog input t ρ (2 ^ 25) hv hbudget hρ
  have e : verifierCompletenessExperimentWithHash A prog input t ρ (2 ^ 25) = (simulateQ keccakCallsOverRandomPermutation
      (Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
        (leanVmProgram (bytecodeWords prog) (publicDigest input))
        (leanVmProver prog s ρ (stackOf prog s w)) (2 ^ 25) >>= fun proof ↦
          verifierWithHash callKeccak256 callKeccakF1600 prog input proof)).run' [] := by
    unfold verifierCompletenessExperimentWithHash
    rw [hAw]
  rw [e]
  exact (Rpm.completenessRpm_at hw (by norm_num)).trans Rpm.completenessRpm_le

/-- **Both parts of `GuestChildComplete`, for a prover that is the specification at a child's
witness**: on valid executions within the cap at a valid rate (`SpecOnValid A ChildFor`), and
everywhere the specification at a child's witness or the empty proof (`ChildSpec`). -/
theorem guestChildComplete_of_spec (A : HonestProverWithHash) (hA : SpecOnValid A ChildFor)
    (hA' : ∀ (prog : Program) (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ),
      ChildSpec A prog input t ρ fuel) :
    (∀ (prog : Program) (input : PublicInput) (t : Execution prog) (ρ : ℕ),
      ValidExecution prog input t → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
      Pr{let v ← (simulateQ LeanVM.keccakCallsOverRandomPermutation (do
          let proof ← A prog input t ρ (2 ^ 25)
          Guest.Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof)).run' []}[v = false] ≤
        (2 : ℝ≥0∞)⁻¹ ^ 126) ∧
    ∀ (s : NodeStatement) (t : Execution Guest.guest) (ρ : ℕ), 2 ^ 22 ≤ t.committedSize →
      s.deferredClaim.HasBytecodeShape (bytecodeWords Guest.guest) →
      let input := PublicInput.ofDigest (statementDigest (deployedSeed Guest.guest) s)
      let proof := Guest.Budget.honestProofWithDeployedKeccakWithHash A Guest.guest input t ρ (2 ^ 25)
      Guest.Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 Guest.guest input proof = true →
      ∃ fresh, LeanVM.Guest.AcceptableChild (bytecodeWords Guest.guest) (deployedSeed Guest.guest)
        ⟨s, fresh, proof⟩ := by
  refine ⟨fun prog input t ρ hv hbudget hρ ↦ ?_, fun s t ρ h22 hsh hacc ↦
    childOk_of_verifierRZ_of (hA' _ _ _ _ _) h22 hsh hacc⟩
  obtain ⟨w, s, hw, hAw⟩ := hA prog input t ρ (2 ^ 25) hv hbudget hρ
  rw [hAw]
  exact (rpmChild_at hw.1 (by norm_num)).trans rpmChild_le

/-! ## The classical provers are instances -/

end LeanVM.Prover
