/-
  LeanVM.E2E.Complete.Node

  One step of V_I on an honest node: the honest proof's head, its word, its single candidate,
  whose execution passes the table check, and the children it decodes.
-/

module

public import LeanVM.E2E.Complete.Stream
public import LeanVM.E2E.Complete.Candidates
public import LeanVM.E2E.Complete.Model

/-!
# V_I's step on an honest node

`nodeStep` (`LeanVM/E2E/Statement.lean`) reads a node's announced sizes and stack root, looks the
root's word up in the idealized proof, checks its shape and Merkle root, and follows every
candidate satisfying the relation without Flock. For a node whose proof is V°'s honest proof of a
stack `q` (`Blind.honestStrategyBlind`), whose word the idealized proof gives (`stackWord`):

* the sizes are the honest ones (`sizesOf_verifierLayout`), the word is well shaped and has the
  announced root (`nodeHead_prove`, `treeRootM_id`);
* the candidates are `q` if it satisfies the relation on the node's input, and none otherwise
  (`blindCandidates_stackWord`, from `eq_of_mem_candidates_deployed` and `thr_le_n`);
* so **`nodeStep_honest`**: when `q`'s execution, if it is a candidate, re-runs and passes the
  table check and decodes the children `cs` at the frames `fr` the idealized proof names for the
  node (decisions E2E-5, E2E-8), the step returns their nodes (none if `q` is no candidate). The
  table check and the decoded children are the guest's completeness
  (`docs/roadmap/t6-completeness.md` L2, L9), stated here as hypotheses.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Whir.Complete LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Whir.Sound

@[expose] public section

/-- The Johnson threshold is at most the block length. -/
theorem thr_le_n (P : LevelCode) : P.thr ≤ P.n := by
  unfold LevelCode.thr
  refine Nat.ceil_le.mpr ?_
  have hn : (0 : ℝ) ≤ P.n := Nat.cast_nonneg _
  exact mul_le_of_le_one_left hn P.hagr

/-- An exact encoding's stack is its candidate. -/
theorem mem_candidates_stackWord {μ R : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits)
    (hR : P₀.R = R) (q : Column μ) : q ∈ Candidates μ R P₀.thr (stackWord μ q) := by
  refine ⟨Finset.univ, ?_, stackWord_agrees μ R q⟩
  rw [Finset.card_univ, Fintype.card_fin]
  have := thr_le_n P₀
  rw [LevelCode.n, hκ, hR] at this
  exact this

/-- **The candidates V_I follows on an honest word**: the honest stack if it satisfies the
relation without Flock on the node's input, none otherwise. -/
theorem blindCandidates_stackWord {prog : Program} {s : Sizes} {ρ : ℕ} (hs : s.Admissible prog)
    (hρ : validRate ρ) (pi : Digest) (q : Column (leanIsaμ prog s)) :
    blindCandidates prog s ρ pi (stackWord (leanIsaμ prog s) q) =
      {q' | q' = q ∧ M3HoldsBlind (leanIsaInstance F₀ prog s) (inputOf pi) q} := by
  have hadm := whirAdmissible prog hs hρ
  obtain ⟨q₀, rest, hc, -⟩ := exists_ladder hadm
  obtain ⟨-, -, hκ, hR, -⟩ := Whir.Params.deployed_spec_hyps hadm hc
  ext q'
  simp only [blindCandidates, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hq', hrel⟩
    obtain rfl := eq_of_mem_candidates_deployed hadm hc hq'
    exact ⟨rfl, hrel⟩
  · rintro ⟨rfl, hrel⟩
    exact ⟨mem_candidates_stackWord _ hκ hR q', hrel⟩

/-- **`sizesOf` reads back admissible sizes** from their verifier layout. -/
theorem sizesOf_verifierLayout {prog : Program} {s : Sizes} (hs : s.Admissible prog) :
    sizesOf prog (verifierLayout prog s) = some s := by
  have hex : ∃ s' : Sizes, verifierLayout prog s' = verifierLayout prog s ∧ s'.Admissible prog :=
    ⟨s, rfl, hs⟩
  unfold sizesOf
  split
  · rename_i h
    exact congrArg some (verifierLayout_injective prog h.choose_spec.1)
  · exact absurd hex ‹_›

/-- The nodes of decoded children: each child's statement digest under the seed, and its
proof. -/
def kidNodes (H : Bytes → Digest) (seed : Digest) (cs : List Node.Child) : List E2E.Node :=
  cs.map fun c ↦ (Id.run (Node.statementDigestWith (fun x ↦ (pure (H x) : Id Digest)) seed c.statement),
    c.proof)

/-- `Id.run` is the identity. -/
theorem id_run_eq {α : Type} (x : Id α) : Id.run x = x := rfl

/-- Appending the decoded children's nodes, one by one. -/
theorem forIn_kids (H : Bytes → Digest) (seed : Digest) :
    ∀ (cs : List Node.Child) (acc : List E2E.Node),
      (forIn (m := Id) cs acc fun c acc' ↦ do
        let pc ← Node.statementDigestWith (fun x ↦ (pure (H x) : Id Digest)) seed c.statement
        pure (ForInStep.yield (acc' ++ [(pc, c.proof)]))) = acc ++ kidNodes H seed cs
  | [], acc => by simp only [List.forIn_nil, kidNodes, List.map_nil, List.append_nil]; rfl
  | c :: cs, acc => by
    simp only [List.forIn_cons]
    exact (forIn_kids H seed cs _).trans
      (by simp only [kidNodes, List.map_cons, List.append_assoc, List.singleton_append]; rfl)

/-- **V_I's step on an honest node.** The node's proof is V°'s honest proof of the stack `q` at
admissible sizes and a valid rate, and the idealized proof gives the node the stack's word and
names the frames `fr` for it. If `q` is a candidate (it satisfies the relation without Flock on the
node's input), its execution re-runs, passes the table check with `H`, and decodes the children
`cs` at the frames `fr`. Then the step returns the children's nodes when `q` is a candidate, and
none otherwise. -/
theorem nodeStep_honest (H : Bytes → Digest) {prog : Program} (seed : Digest) (ip : IdealProof)
    {s : Sizes} {ρ : ℕ} {q : Column (leanIsaμ prog s)} {input : PublicInput}
    (hs : s.Admissible prog) (hρ : validRate ρ) {sd : Digest} {fuel : ℕ} {π : Proof}
    (hπ : prove H (blindProgram (bytecodeWords prog) (publicDigest input))
      (Blind.honestStrategyBlind prog s ρ q) sd fuel = some π)
    (pi : Digest) (hword : ip.word (pi, π) = some (stackWord (leanIsaμ prog s) q))
    {fr : String → List E → Option ℕ} (hfr : ip.frames (pi, π) = fr) (cs : List Node.Child)
    (hcand : M3HoldsBlind (leanIsaInstance F₀ prog s) (inputOf pi) q →
      ∃ t, candidateRun prog s q = some t ∧
        tableOKWith (m := Id) (fun x ↦ (pure (H x) : Id Digest)) (t.blakeRows blakeFree) = true ∧
        (Guest.End.decodeAt (Guest.Value.tableSem (t.blakeRows blakeFree)) fr
          t.image).witness.children = cs) :
    nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog seed ip (pi, π) =
      some (open Classical in
        if M3HoldsBlind (leanIsaInstance F₀ prog s) (inputOf pi) q then kidNodes H seed cs else []) := by
  obtain ⟨level, rest, hc, hann, hroot, hshape⟩ := nodeHead_prove H hs hρ hπ
  have hadm := whirAdmissible prog hs hρ
  obtain ⟨hfold, -⟩ := Whir.Params.deployed_spec_hyps hadm hc
  have hW := hword
  obtain rfl := hfr
  have hshaped : WellShaped (2 ^ level.fold) (stackWord (leanIsaμ prog s) q) := by
    rw [hfold]; exact wellShaped_stackWord _ q
  unfold nodeStep
  have hw2 : (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).2 = 2 ^ level.fold := rfl
  simp only [hann, sizesOf_verifierLayout hs, hroot, hshape, hW, ↓reduceIte, treeRootM_id, hw2,
    hshaped, not_true_eq_false]
  have hht : (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).1 =
      stackHeight (leanIsaμ prog s) level := rfl
  have hr : treeRoot (fun x ↦ (pure (H x) : Id Digest)) (stackHeight (leanIsaμ prog s) level)
      (stackWord (leanIsaμ prog s) q) = treeRoot H (stackHeight (leanIsaμ prog s) level)
      (stackWord (leanIsaμ prog s) q) := rfl
  simp only [hht, hr, ne_eq]
  have hset := blindCandidates_stackWord hs hρ pi q
  by_cases hm : M3HoldsBlind (leanIsaInstance F₀ prog s) (inputOf pi) q
  · have hfin : (blindCandidates prog s ρ pi (stackWord (leanIsaμ prog s) q)).Finite := by
      rw [hset]; exact (Set.finite_singleton q).subset fun x hx ↦ hx.1
    have hlist : hfin.toFinset.toList = [q] := by
      have : hfin.toFinset = {q} := by
        ext x
        simp only [Set.Finite.mem_toFinset, hset, Set.mem_ofPred_eq, Finset.mem_singleton]
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hm⟩⟩
      rw [this, Finset.toList_singleton]
    obtain ⟨t, hrun, htab, hkids⟩ := hcand hm
    simp only [hm, ↓reduceIte]
    split
    · rename_i h
      rw [hlist]
      simp only [List.forIn_cons, List.forIn_nil, hrun, htab, hkids]
      rw [forIn_kids]
      show Id.run _ = _
      simp only [Id.run_bind, id_run_eq (treeRoot H _ _), ↓reduceIte, not_true_eq_false,
        List.nil_append]
      rfl
    · exact absurd hfin ‹_›
  · have hfin : (blindCandidates prog s ρ pi (stackWord (leanIsaμ prog s) q)).Finite := by
      rw [hset]; exact Set.finite_empty.subset fun x hx ↦ hm hx.2
    have hlist : hfin.toFinset.toList = [] := by
      have : hfin.toFinset = ∅ := by
        ext x
        simp only [Set.Finite.mem_toFinset, hset, Set.mem_ofPred_eq, Finset.notMem_empty,
          iff_false, not_and]
        exact fun _ ↦ hm
      rw [this, Finset.toList_empty]
    simp only [hm, ↓reduceIte]
    split
    · rw [hlist]
      show Id.run _ = _
      simp only [Id.run_bind, id_run_eq (treeRoot H _ _), List.forIn_nil]
      rfl
    · exact absurd hfin ‹_›

/-! ## The closure -/

/-- **The closure accepts good nodes within their size.** Good nodes step to good children, a
good node's size exceeds its children's total; then from good nodes of total size at most `fuel`
the closure accepts. -/
theorem closure_accepts (H : Bytes → Digest) (prog : Program) (seed : Digest) (ip : IdealProof)
    (Good : E2E.Node → Prop) (kidsOf : E2E.Node → List E2E.Node) (sz : E2E.Node → ℕ)
    (hstep : ∀ ν, Good ν →
      nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog seed ip ν = some (kidsOf ν))
    (hkids : ∀ ν, Good ν → ∀ κ ∈ kidsOf ν, Good κ)
    (hsz : ∀ ν, Good ν → ((kidsOf ν).map sz).sum + 1 ≤ sz ν) :
    ∀ (fuel : ℕ) (todo done : List E2E.Node), (∀ ν ∈ todo, Good ν) →
      (todo.map sz).sum ≤ fuel →
      closure (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog seed ip fuel todo done = true
  | _, [], _, _, _ => by simp only [closure]; rfl
  | 0, ν :: todo, done, hg, hf => by
    have := hsz ν (hg ν List.mem_cons_self)
    simp only [List.map_cons, List.sum_cons] at hf
    omega
  | fuel + 1, ν :: todo, done, hg, hf => by
    have hν := hg ν List.mem_cons_self
    have h1 := hsz ν hν
    simp only [List.map_cons, List.sum_cons] at hf
    have hrest : ∀ κ ∈ todo, Good κ := fun κ hκ ↦ hg κ (List.mem_cons_of_mem ν hκ)
    simp only [closure]
    split
    · exact closure_accepts H prog seed ip Good kidsOf sz hstep hkids hsz fuel todo done hrest
        (by omega)
    · show Id.run _ = _
      rw [Id.run_bind, hstep ν hν]
      refine closure_accepts H prog seed ip Good kidsOf sz hstep hkids hsz fuel _ _ ?_ ?_
      · intro κ hκ
        rcases List.mem_append.mp hκ with hκ | hκ
        · exact hrest κ hκ
        · exact hkids ν hν κ hκ
      · rw [List.map_append, List.sum_append]
        omega

/-! ## The root -/

/-- **The outer checks pass** on a statement whose DA claims carry their roots' vector digests
and whose deferred claim's bytecode part is true. -/
theorem outerChecksWith_true (H : Bytes → Digest) (prog : Program) (s : Node.NodeStatement)
    (hda : ∀ c ∈ s.claims.da,
      Da.toBytes c.2 = Id.run (Da.vectorDigestOfWith (fun x ↦ (pure (H x) : Id Digest)) c.1))
    (hbc : s.defer.BytecodeHolds (bytecodeWords prog)) :
    outerChecksWith (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog s = true := by
  unfold outerChecksWith
  show Id.run _ = _
  rw [Id.run_bind]
  have hall := allM_id_true (fun c : Node.DaClaim ↦ do
      pure (decide (Da.toBytes c.2 = (← Da.vectorDigestOfWith
        (fun x ↦ (pure (H x) : Id Digest)) c.1)))) s.claims.da
      fun c hc ↦ decide_eq_true (hda c hc)
  rw [show (List.allM _ s.claims.da : Id Bool).run = true from hall]
  simp [hbc]

/-- **V_I accepts** when V° accepts the root's proof on the root's digest, the outer checks
pass, and the root node is good for the closure within the fuel. -/
theorem idealVerify_accepts (H : Bytes → Digest) (prog : Program) (ip : IdealProof) (fuel : ℕ)
    (s : Node.NodeStatement)
    (hV : Id.run (Verifier.verifyBlindWith (m := Id) (fun x ↦ (pure (H x) : Id Digest))
      (bytecodeWords prog) (Id.run (Node.statementDigestWith (fun x ↦ (pure (H x) : Id Digest))
        (Id.run (fiatShamirIvWith (fun x ↦ (pure (H x) : Id Digest)) (bytecodeWords prog))) s))
      ip.proof) = true)
    (hout : outerChecksWith (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog s = true)
    (hcl : closure (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog
      (Id.run (fiatShamirIvWith (fun x ↦ (pure (H x) : Id Digest)) (bytecodeWords prog))) ip fuel
      [(Id.run (Node.statementDigestWith (fun x ↦ (pure (H x) : Id Digest))
        (Id.run (fiatShamirIvWith (fun x ↦ (pure (H x) : Id Digest)) (bytecodeWords prog))) s),
        ip.proof)] [] = true) :
    idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog ip fuel s = true := by
  unfold idealVerify
  show Id.run _ = _
  rw [Id.run_bind, Id.run_bind, Id.run_bind]
  simp only [hV, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [Id.run_bind]
  simp only [hout]
  exact hcl

end
end LeanVM.E2E.Complete
