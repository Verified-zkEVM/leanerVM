import XmssSecurity.Proof.ExactKeygenQueryCount
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# The verifier's hash calls

`Concrete.verify` makes at most `verifyHashBound = 2 (1 + v (2^w - 1) + 1 + h)` hash calls: per layer
the digest, the chain walks, the leaf and the authentication path.
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-- The verifier's hash calls: two layers of a digest, `v` chain walks, a leaf and a path. -/
def verifyHashBound : Nat := 2 * (1 + numChains * (chainLength - 1) + 1 + treeHeight)

namespace Concrete

private abbrev AnyInput : HashInput → Prop := fun _ => True

theorem tweakableHash_queryBound_one (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    (tweakableHash parameter domain payload : OracleComp HashSpec Digest).IsQueryBoundP
      AnyInput 1 := by
  simp [tweakableHash, oracleHash]

theorem sequenceFin_queryBound_mul {α : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) (bound : Nat)
    (hbound : ∀ index, (computation index).IsQueryBoundP AnyInput bound) :
    (sequenceFin computation).IsQueryBoundP AnyInput (n * bound) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin]
      refine (OracleComp.isQueryBoundP_bind (hbound 0) fun head _ =>
        OracleComp.isQueryBoundP_bind
          (ih (fun index => computation index.succ) fun index => hbound index.succ)
          fun tail _ => OracleComp.isQueryBoundP_pure (p := AnyInput) _ 0).mono ?_
      rw [Nat.succ_mul]
      omega

theorem chainWalk_queryBound_steps (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    (chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP AnyInput steps := by
  induction steps with
  | zero => simp [chainWalk]
  | succ steps ih =>
      rw [chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 1) ih fun previous _ => ?_
      split
      · exact tweakableHash_queryBound_one _ _ _
      · exact (OracleComp.isQueryBoundP_pure (p := AnyInput) _ 0).mono (by omega)

theorem topChainWalk_queryBound_steps (parameter : PublicParameter) (key : TopIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    (topChainWalk parameter key chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP AnyInput steps := by
  induction steps with
  | zero => simp [topChainWalk]
  | succ steps ih =>
      rw [topChainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 1) ih fun previous _ => ?_
      split
      · exact tweakableHash_queryBound_one _ _ _
      · exact (OracleComp.isQueryBoundP_pure (p := AnyInput) _ 0).mono (by omega)

theorem authenticationRoot_queryBound_levels (parameter : PublicParameter)
    (leafIndex : LeafIndex) (signature : Signature) (levels : Nat) (leaf : Digest) :
    (authenticationRoot parameter leafIndex signature levels leaf :
      OracleComp HashSpec Digest).IsQueryBoundP AnyInput levels := by
  induction levels with
  | zero => simp [authenticationRoot]
  | succ levels ih =>
      rw [authenticationRoot]
      refine OracleComp.isQueryBoundP_bind (m := 1) ih fun current _ => ?_
      unfold authenticationNodeHash
      split
      · split
        · exact tweakableHash_queryBound_one _ _ _
        · exact tweakableHash_queryBound_one _ _ _
      · exact (OracleComp.isQueryBoundP_pure (p := AnyInput) _ 0).mono (by omega)

theorem topAuthenticationRoot_queryBound_levels (parameter : PublicParameter)
    (key : TopIndex) (path : Fin treeHeight → Digest) (levels : Nat) (leaf : Digest) :
    (topAuthenticationRoot parameter key path levels leaf :
      OracleComp HashSpec Digest).IsQueryBoundP AnyInput levels := by
  induction levels with
  | zero => simp [topAuthenticationRoot]
  | succ levels ih =>
      rw [topAuthenticationRoot]
      refine OracleComp.isQueryBoundP_bind (m := 1) ih fun current _ => ?_
      split
      · split
        · exact tweakableHash_queryBound_one _ _ _
        · exact tweakableHash_queryBound_one _ _ _
      · exact (OracleComp.isQueryBoundP_pure (p := AnyInput) _ 0).mono (by omega)

attribute [local irreducible] topAuthenticationRoot in
theorem verifyTop_queryBound (publicKey : PublicKey) (key : TopIndex) (root : Digest)
    (part : LayerSignature) :
    (verifyTop publicKey key root part : OracleComp HashSpec Bool).IsQueryBoundP AnyInput
      (1 + numChains * (chainLength - 1) + 1 + treeHeight) := by
  unfold verifyTop
  refine (OracleComp.isQueryBoundP_bind (n := 1)
    (m := numChains * (chainLength - 1) + 1 + treeHeight)
    (tweakableHash_queryBound_one publicKey.parameter (.topEncoding key)
      (topEncodingPayload root part.randomness)) fun digest _ => ?_).mono (by omega)
  split
  · refine (OracleComp.isQueryBoundP_bind
      (sequenceFin_queryBound_mul _ (chainLength - 1) fun chain =>
        (topChainWalk_queryBound_steps _ _ _ _ _ _).mono (Nat.sub_le _ _))
      fun endpoints _ => OracleComp.isQueryBoundP_bind
        (tweakableHash_queryBound_one publicKey.parameter (.topLeaf key) (leafPayload endpoints))
        fun leaf _ => OracleComp.isQueryBoundP_bind
          (topAuthenticationRoot_queryBound_levels _ _ _ _ _)
          fun topRoot _ => OracleComp.isQueryBoundP_pure (p := AnyInput) _ 0).mono ?_
    simp only [add_zero]
    omega
  · exact (OracleComp.isQueryBoundP_pure (p := AnyInput) _ 0).mono (Nat.zero_le _)

-- The paths are folded at the literal `treeHeight`; keep elaboration from unrolling them.
attribute [local irreducible] authenticationRoot topAuthenticationRoot

theorem verifyAfterLeaf_queryBound (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    (verifyAfterLeaf publicKey leafIndex signature leaf : OracleComp HashSpec Bool).IsQueryBoundP
      AnyInput (treeHeight + (1 + numChains * (chainLength - 1) + 1 + treeHeight)) := by
  unfold verifyAfterLeaf
  exact OracleComp.isQueryBoundP_bind (authenticationRoot_queryBound_levels _ _ _ _ _)
    fun _ _ => verifyTop_queryBound _ _ _ _

theorem verify_queryBound (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    (verify publicKey leafIndex message signature : OracleComp HashSpec Bool).IsQueryBoundP
      AnyInput verifyHashBound := by
  unfold verify
  refine (OracleComp.isQueryBoundP_bind (n := 1)
    (m := numChains * (chainLength - 1) + 1 + treeHeight +
      (1 + numChains * (chainLength - 1) + 1 + treeHeight))
    (tweakableHash_queryBound_one publicKey.parameter (.encoding leafIndex)
      (encodingPayload message signature.randomness)) fun digest _ => ?_).mono
    (by simp only [verifyHashBound]; omega)
  split
  · refine (OracleComp.isQueryBoundP_bind
      (sequenceFin_queryBound_mul _ (chainLength - 1) fun chain =>
        (chainWalk_queryBound_steps _ _ _ _ _ _).mono (Nat.sub_le _ _))
      fun endpoints _ => OracleComp.isQueryBoundP_bind
        (tweakableHash_queryBound_one publicKey.parameter (.leaf leafIndex) (leafPayload endpoints))
        fun leaf _ => verifyAfterLeaf_queryBound publicKey leafIndex signature leaf).mono ?_
    omega
  · exact (OracleComp.isQueryBoundP_pure (p := AnyInput) _ 0).mono (Nat.zero_le _)

end Concrete

open ExactQueryCount in
/-- The model's verification, in the oracle world: at most `verifyHashBound` hash calls. -/
theorem scheme_verify_isHashQueryBound (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    (Concrete.scheme.verify publicKey leafIndex message signature).IsQueryBoundP IsHashQuery
      verifyHashBound := by
  change (liftM (Concrete.verify publicKey leafIndex message signature :
    OracleComp HashSpec Bool) : OracleComp OracleWorld Bool).IsQueryBoundP IsHashQuery _
  exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ : HashInput => True)
    (q := IsHashQuery) (fun _ => iff_of_true trivial rfl)
    (Concrete.verify_queryBound publicKey leafIndex message signature)

end XmssSecurity
