/-
  LeanVM.Guest.Child.Deployed

  The deployed half of `GuestChildComplete`: the child prover's proof with Keccak of a guest
  execution of committed size in `[2^22, 2^28]`, when the verifier refusing a zero challenge
  accepts it, is with its statement and the claims its run evaluates a child the guest accepts.
-/

module

public import LeanVM.Guest.Child.Merkle
public import LeanVM.Guest.Child.StackLog
public import LeanVM.Guest.Start
public import LeanVM.Guest.Child.RefuseZero
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.WithHashBridge
public import LeanVM.Guest.WithHash

/-!
# Honest children at Keccak

`childOk_of_verifierRZ`: from the acceptance of the verifier refusing a zero challenge
(`Budget.verifierRefusingZero`, which accepts only what `Budget.verifierNZ` does) at Keccak, of
the child prover's proof (`childProver`), when it makes one, of a guest execution on a statement's
digest under the deployed seed:

* the deferring verifier refusing a zero challenge accepts it with the claim its run evaluates,
  a true claim (`run_claimed_of_computed`): `noZeroChallenge`, and so `verifies`
  (`Limits.verifyDeferred_of_nz`) and `stream` (`stream_le_of_verifyDeferred`);
* the proof is the pure prover's (`prove_of_some`), whose stream starts with the honest
  sizes, of the execution's committed size (`muMin_le_announced`): `stackLog`;
* its query steps under the deferring program are the verifier program's (`queriesOf_le`, the
  claim being true), which are honest batches in range (`queriesOf_proveFrom`,
  `inRange_leanVmProgram`), which agree (`batchAgrees_honest`): `capsAgree`.
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.KeccakHash LeanVM.Node LeanVM.Guest.End
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- **An accepted proof of a prover that is the specification at a child's witness (or makes no
proof) is a child the guest accepts.** -/
theorem childOk_of_verifierRZ_of {A : HonestProverWithHash} {s : NodeStatement}
    {t : Execution guest} {ρ : ℕ}
    (hA : ChildSpec A guest (publicInputOf (statementDigest (deployedSeed guest) s)) t ρ (2 ^ 25))
    (h22 : 2 ^ 22 ≤ t.committedSize) (hsh : s.deferredClaim.HasBytecodeShape bytecode)
    {proof : Proof}
    (hsome : Budget.honestProofWithDeployedKeccakWithHash A guest
      (publicInputOf (statementDigest (deployedSeed guest) s)) t ρ (2 ^ 25) = some proof)
    (hacc : Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 guest
      (publicInputOf (statementDigest (deployedSeed guest) s)) proof = true) :
    ∃ fresh, LeanVM.Guest.AcceptableChild bytecode (deployedSeed guest) ⟨s, fresh, proof⟩ := by
  set d := statementDigest (deployedSeed guest) s with hd
  have hpd : publicDigest (publicInputOf d) = d := publicDigest_publicInputOf d
  -- the claim the run evaluates
  have hacc' := hacc
  rw [verifierRZ_eq] at hacc'
  obtain ⟨c, hc, hrz⟩ := runProof_claimed_of_computed_rz keccak256 keccakF1600
    verifyStackedOpening (bytecodeWords guest) (publicDigest (publicInputOf d)) hacc'
  rw [hpd] at hrz
  have hRZ : Limits.verifyDeferredRefusingZero bytecode (deployedSeed guest) d c proof = true := by
    rw [Limits.verifyDeferredRefusingZero_eq_withHash, deferredProgram_eq]
    exact hrz
  have hV := Limits.verifyDeferred_of_nz (verifyDeferredNZ_of_rz hRZ)
  -- the pure prover's proof
  obtain ⟨w, sz, hchild, hprove⟩ := prove_of_some hA hsome
  obtain ⟨⟨hρ, hw, hs, hadm, -⟩, -⟩ := id hchild
  obtain ⟨rest, hrest⟩ := stream_prefix keccak256 keccakF1600 hprove
  refine ⟨c, ⟨hsh, hV, ?_, stream_le_of_verifyDeferred hV, ?_, hRZ⟩⟩
  · -- the stack log
    show ∀ layout r, announced bytecode proof.stream = some (layout, r) → _
    rw [hrest]
    exact muMin_le_announced hchild h22 rest
  · -- the caps
    intro b hb
    have hle : Prog.Le (deferredProgram c bytecode d) (leanVmProgram bytecode d) := by
      rw [deferredProgram_eq, leanVmProgram_eq]
      exact .bind (verifyExecution_le (claimed_le_computed hc) d) fun _ ↦ .refl _
    have hb' := queriesOf_le hle hb
    have hq := m3Honest_stackOf hw hs
    have hrun := runI_leanVmProgram (input := publicInputOf d) hadm hρ hq
    have hacc0 := Strategy.acceptsFrom_of_runFrom _ [] (fun chal ↦ (hrun chal).1)
      (fun chal ↦ (hrun chal).2)
    unfold prove at hprove
    obtain ⟨tt, htt, he⟩ := Option.map_eq_some_iff.mp hprove
    rw [hpd] at htt hacc0
    have hir := inRange_leanVmProgram bytecode d
    have := queriesOf_proveFrom _ (2 ^ 25) (leanVmProgram bytecode d) [] _ tt.1 tt.2 [] []
      hacc0 (by simp [commits]) (by simpa [commits] using hir) htt b
    obtain ⟨ht, word, ps, rfl, hps⟩ := this (by
      have e : proof = ⟨tt.1, tt.2⟩ := he.symm
      simp only [List.append_nil, rootsOf, commits, List.map_nil]
      rw [e] at hb'
      exact hb')
    exact batchAgrees_honest hps

/-- **The child prover's accepted proof is a child the guest accepts.** -/
theorem childOk_of_verifierRZ {s : NodeStatement} {t : Execution guest} {ρ : ℕ}
    (h22 : 2 ^ 22 ≤ t.committedSize) (hsh : s.deferredClaim.HasBytecodeShape bytecode)
    {proof : Proof}
    (hsome : Budget.honestProofWithDeployedKeccakWithHash childProver guest
      (publicInputOf (statementDigest (deployedSeed guest) s)) t ρ (2 ^ 25) = some proof)
    (hacc : Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 guest
      (publicInputOf (statementDigest (deployedSeed guest) s)) proof = true) :
    ∃ fresh, LeanVM.Guest.AcceptableChild bytecode (deployedSeed guest) ⟨s, fresh, proof⟩ :=
  childOk_of_verifierRZ_of (childSpec_childProver _ _ _ _ _) h22 hsh hsome hacc

end
end LeanVM.Guest.Child
