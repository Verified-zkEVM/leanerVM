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

/-!
# Honest children at Keccak

`childOk_of_verifierRZ`: from the acceptance of the verifier refusing a zero challenge
(`Budget.verifierRZ`, which accepts only what `Budget.verifierNZ` does) at Keccak, of the child prover's proof (`childProver`), of a guest execution
on a statement's digest under the deployed seed:

* the deferring verifier refusing a zero challenge accepts it with the claim its run evaluates,
  a true claim (`run_claimed_of_computed`): `noZeroChallenge`, and so `verifies`
  (`Limits.verifyDeferred_of_nz`) and `stream` (`stream_le_of_verifyDeferred`);
* the proof is the pure prover's (`prove_of_verifierNZ`), whose stream starts with the honest
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

/-- An accepted run with the computed value is accepted with a true claim. -/
theorem runProof_claimed_of_computed (H : Bytes → Id Digest) (F : KState → Id KState)
    (opening : ℕ → ℕ → List StackClaim → Prog Unit) (bytecode : List K) (publicInput : Digest)
    {sd : KState} {π : Proof}
    (h : Id.run (runProof H F ((execWith computedValue opening bytecode publicInput).bind
      fun _ ↦ Prog.ret true) sd π) = true) :
    ∃ c : FixedClaims, c.Holds bytecode ∧
      Id.run (runProof H F ((execWith (claimedValue c) opening bytecode publicInput).bind
        fun _ ↦ Prog.ret true) sd π) = true := by
  unfold runProof at h ⊢
  revert h
  match hr : Compile.run H F ((execWith computedValue opening bytecode publicInput).bind
      fun _ ↦ Prog.ret true) ⟨⟨sd, []⟩, π.stream, π.openings, []⟩ with
  | some (true, s) =>
    intro h
    obtain ⟨c, hc, e⟩ := run_claimed_of_computed H F opening bytecode publicInput _ hr
    refine ⟨c, hc, ?_⟩
    rw [e]
    exact h
  | some (false, _) => intro h; cases h
  | none => intro h; cases h

/-- **An accepted proof of a prover that is the specification at a child's witness (or the empty
proof) is a child the guest accepts.** -/
theorem childOk_of_verifierRZ_of {A : HonestProver} {s : NodeStatement} {t : Trace guest} {ρ : ℕ}
    (hA : ChildSpec A guest (publicInputOf (statementDigest (deployedSeed guest) s)) t ρ (2 ^ 25))
    (h22 : 2 ^ 22 ≤ t.committedSize) (hsh : s.defer.Shaped bytecode)
    (hacc : Budget.verifierRZ (m := Id) keccak256 keccakF guest
      (publicInputOf (statementDigest (deployedSeed guest) s))
      (Budget.atKeccak A guest (publicInputOf (statementDigest (deployedSeed guest) s))
        t ρ (2 ^ 25)) = true) :
    ∃ fresh, LeanVM.Guest.ChildOk bytecode (deployedSeed guest) ⟨s, fresh,
      Budget.atKeccak A guest (publicInputOf (statementDigest (deployedSeed guest) s))
        t ρ (2 ^ 25)⟩ := by
  set d := statementDigest (deployedSeed guest) s with hd
  set proof := Budget.atKeccak A guest (publicInputOf d) t ρ (2 ^ 25) with hproof
  have hpd : publicDigest (publicInputOf d) = d := publicDigest_publicInputOf d
  -- the claim the run evaluates
  have hacc' := hacc
  rw [verifierRZ_eq] at hacc'
  obtain ⟨c, hc, hrz⟩ := runProof_claimed_of_computed_rz keccak256 keccakF
    verifyStackedOpening (bytecodeWords guest) (publicDigest (publicInputOf d)) hacc'
  rw [hpd] at hrz
  have hRZ : Limits.verifyDeferredRZ bytecode (deployedSeed guest) d c proof = true := by
    unfold Limits.verifyDeferredRZ
    rw [deferredProgram_eq]
    exact hrz
  have hV := Limits.verifyDeferred_of_nz (verifyDeferredNZ_of_rz hRZ)
  -- the pure prover's proof
  obtain ⟨w, sz, hchild, hprove⟩ := prove_of_verifierNZ_of hA (verifierNZ_of_rz hacc)
  obtain ⟨⟨hρ, hw, hs, hadm, -⟩, -⟩ := id hchild
  obtain ⟨rest, hrest⟩ := stream_prefix keccak256 keccakF hprove
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
theorem childOk_of_verifierRZ {s : NodeStatement} {t : Trace guest} {ρ : ℕ}
    (h22 : 2 ^ 22 ≤ t.committedSize) (hsh : s.defer.Shaped bytecode)
    (hacc : Budget.verifierRZ (m := Id) keccak256 keccakF guest
      (publicInputOf (statementDigest (deployedSeed guest) s))
      (Budget.atKeccak childProver guest (publicInputOf (statementDigest (deployedSeed guest) s))
        t ρ (2 ^ 25)) = true) :
    ∃ fresh, LeanVM.Guest.ChildOk bytecode (deployedSeed guest) ⟨s, fresh,
      Budget.atKeccak childProver guest (publicInputOf (statementDigest (deployedSeed guest) s))
        t ρ (2 ^ 25)⟩ :=
  childOk_of_verifierRZ_of (childSpec_childProver _ _ _ _ _) h22 hsh hacc

end
end LeanVM.Guest.Child
