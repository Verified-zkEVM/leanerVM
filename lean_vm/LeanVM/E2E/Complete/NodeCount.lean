/-
  LeanVM.E2E.Complete.NodeCount

  V_I's queries on an honest node: the stack's Merkle tree, the table check of its single
  candidate, and its children's digests.
-/

module

public import LeanVM.E2E.Complete.Node
public import LeanVM.E2E.BudgetCount

/-!
# V_I's queries on an honest node

`nodeStep_honest`'s count (`Node.lean`): on a node whose proof is V°'s honest proof of a stack `q`
and whose word the idealized proof gives as `q`'s full word, V_I's step hashes the word's Merkle
tree, at most `2^(costHeight+1) − 1` queries (`count_pTreeRootM_le`, `stackShape_height_le`);
then, if `q` satisfies the relation without Flock, it is the single candidate
(`blindCandidates_stackWord`), whose table check and decoded children's digests (five each) it
makes. So **`count_nodeStep_honest`**: at most `2^(costHeight+1) − 1 + T + 5K` queries when the
candidate's table check makes at most `T` and it decodes at most `K` children.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Whir.Complete LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Whir.Sound

@[expose] public section

/-- The value of a counted partial tree's root is the `Id` root. -/
theorem val_pTreeRootM (H : Bytes → Digest) (ht : ℕ) (P : PWord) :
    (pTreeRootM (countQuery H) ht P).val = pTreeRootM (m := Id) (fun x ↦ pure (H x)) ht P :=
  rel_pTreeRootM (fun {α : Type} (x : Counted α) (y : Id α) ↦ ValRel x y) valRel_pure valRel_bind
    (countQuery H) _ (fun _ ↦ rfl) ht P

/-- **V_I's queries on an honest node**: the word's Merkle tree, the single candidate's table
check (at most `T`) and its decoded children's digests (at most `K` children, five queries
each). -/
theorem count_nodeStep_honest (H : Bytes → Digest) {prog : Program} (seed : Digest)
    (ip : IdealProof) {s : Sizes} {ρ : ℕ} {q : Column (leanIsaμ prog s)} {input : PublicInput}
    (hs : s.Admissible prog) (hρ : validRate ρ) {sd : Digest} {fuel : ℕ} {π : Proof}
    (hπ : prove H (blindProgram (bytecodeWords prog) (publicDigest input))
      (Blind.honestStrategyBlind prog s ρ q) sd fuel = some π)
    (pi : Digest) (hword : ip.word (pi, π) = some (PWord.full (stackWord (leanIsaμ prog s) q)))
    {fr : String → List E → Option ℕ} (hfr : ip.frames (pi, π) = fr) (T K : ℕ)
    (hcand : M3HoldsBlind (leanIsaInstance F₀ prog s) (inputOf pi) q →
      ∃ t, candidateRun prog s q = some t ∧
        (tableOKWith (countQuery H) (t.blakeRows blakeFree)).count ≤ T ∧
        (Guest.End.decodeAt (Guest.Value.tableSem (t.blakeRows blakeFree)) fr
          t.image).witness.children.length ≤ K) :
    (nodeStep (countQuery H) prog seed ip (pi, π)).count + 1 ≤
      2 ^ (costHeight + 1) + (T + 5 * K) := by
  obtain ⟨level, rest, hc, hann, hroot, hshape⟩ := nodeHead_prove H hs hρ hπ
  have hadm := whirAdmissible prog hs hρ
  obtain ⟨hfold, -⟩ := Whir.Params.deployed_spec_hyps hadm hc
  have hW := hword
  obtain rfl := hfr
  have hshaped : WellShaped (2 ^ level.fold) (stackWord (leanIsaμ prog s) q) := by
    rw [hfold]; exact wellShaped_stackWord _ q
  have hht := stackShape_height_le hshape
  have hht' : stackHeight (leanIsaμ prog s) level =
      (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).1 := rfl
  rw [hht'] at hroot
  unfold nodeStep
  have hw2 : (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).2 = 2 ^ level.fold := rfl
  simp only [hann, sizesOf_verifierLayout hs, hroot, hshape, hW, ↓reduceIte, PWord.word_full,
    PWord.full_full, hw2, hshaped, not_true_eq_false, and_false]
  rw [Counted.count_bind]
  have hp := count_pTreeRootM_le H (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).1
    (PWord.full (stackWord (leanIsaμ prog s) q))
  have hpow : 2 ^ ((levelShape (leanIsaμ prog s) level (2 ^ level.fold)).1 + 1) ≤
      2 ^ (costHeight + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by unfold levelShape; simp only; omega)
  rw [val_pTreeRootM, pTreeRootM_full]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  refine (fun (x : Counted (Option (List E2E.Node))) (hx : x.count ≤ T + 5 * K) ↦
    (show _ + x.count + 1 ≤ _ by omega)) _ ?_
  have hset : blindCandidatesS prog s ρ (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).1 pi
      (PWord.full (stackWord (leanIsaμ prog s) q)) =
        {q' | q' = q ∧ M3HoldsBlind (leanIsaInstance F₀ prog s) (inputOf pi) q} :=
    (blindCandidatesS_full prog s ρ (stackHeight (leanIsaμ prog s) level) pi
      (stackWord (leanIsaμ prog s) q)).trans (blindCandidates_stackWord hs hρ pi q)
  split
  · rename_i hfin
    rw [Counted.count_bind]
    by_cases hm : M3HoldsBlind (leanIsaInstance F₀ prog s) (inputOf pi) q
    · have hlist : hfin.toFinset.toList = [q] := by
        have : hfin.toFinset = {q} := by
          ext x
          simp only [Set.Finite.mem_toFinset, hset, Set.mem_ofPred_eq, Finset.mem_singleton]
          exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hm⟩⟩
        rw [this, Finset.toList_singleton]
      obtain ⟨t, hrun, htab, hkids⟩ := hcand hm
      rw [hlist, List.forIn_cons, Counted.count_bind]
      simp only [hrun, List.forIn_nil, Counted.count_bind, Counted.val_bind]
      split
      · simp
        omega
      · simp only [Counted.count_bind, Counted.count_pure, Counted.val_bind, Counted.val_pure,
          Nat.add_zero]
        have hf := count_forIn_le (fun (c : Node.Child) (acc : List E2E.Node) ↦
          (do
            let pc ← Node.statementDigestWith (countQuery H) seed c.statement
            pure (ForInStep.yield (acc ++ [(pc, c.proof)])) : Counted _)) (fun _ ↦ 5)
          (fun a b ↦ by simp [count_statementDigestWith])
          (Guest.End.decodeAt (Guest.Value.tableSem (Trace.blakeRows blakeFree t))
            (ip.frames (pi, π)) t.image).witness.children []
        simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hf
        omega
    · have hlist : hfin.toFinset.toList = [] := by
        have : hfin.toFinset = ∅ := by
          ext x
          simp only [Set.Finite.mem_toFinset, hset, Set.mem_ofPred_eq, Finset.notMem_empty,
            iff_false, not_and]
          exact fun _ ↦ hm
        rw [this, Finset.toList_empty]
      rw [hlist]
      simp
  · simp

end
end LeanVM.E2E.Complete
