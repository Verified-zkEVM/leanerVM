/-
  LeanVM.E2E.Reduction.VerifyBound

  The hash queries of leanXMSS's verification: per layer the message digest, the chain walks,
  the leaf and the authentication path.
-/

module

public import LeanVM.E2E.Reduction.Count

/-!
# leanXMSS's verification makes at most `xmssVerifyBound` hash queries

`LeanXmss.Concrete.verify` recovers two layers' roots; each makes one query for the message
digest, at most `chainLength - 1` per chain walk, one for the leaf and one per tree level
(`xmssVerifyBound = 2 (1 + v (chainLength - 1) + 1 + layerHeight)`, `verify_isTotalQueryBound`).
It is the final verification's `cx` of the leanXMSS reduction (`aggregate_no_forgery`).
-/

namespace LeanVM.E2E

open OracleSpec OracleComp LeanXmss LeanXmss.Concrete

@[expose] public section

/-- The hash queries of leanXMSS's verification. -/
def xmssVerifyBound : ℕ := 2 * (1 + numChains * (chainLength - 1) + 1 + layerHeight)

/-- A tweakable hash makes one query. -/
theorem tweakableHash_isTotalQueryBound (p : PublicParameter) (d : HashDomain) (x : HashInput) :
    IsTotalQueryBound (tweakableHash p d x : OracleComp LeanXmss.HashSpec Digest) 1 := by
  simp only [tweakableHash, oracleHash]
  change IsTotalQueryBound ((liftM (LeanXmss.HashSpec.query (tweakableHashInput p d x)) :
    OracleComp LeanXmss.HashSpec _) >>= fun o ↦ pure (truncateHash o)) 1
  exact isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- A chain walk of `steps` steps makes at most `steps` queries. -/
theorem chainWalk_isTotalQueryBound (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (c : ChainIndex) (start : ℕ) :
    ∀ (steps : ℕ) (v : Digest),
      IsTotalQueryBound (chainWalk p lay key c start steps v : OracleComp LeanXmss.HashSpec Digest) steps
  | 0, _ => trivial
  | steps + 1, v => by
    simp only [chainWalk]
    refine isTotalQueryBound_bind (chainWalk_isTotalQueryBound p lay key c start steps v)
      fun _ ↦ ?_
    split
    · exact tweakableHash_isTotalQueryBound _ _ _
    · trivial

/-- A one-time leaf makes at most the digest's, the chain walks' and the leaf's queries. -/
theorem otsLeaf_isTotalQueryBound (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (msg : HashInput) (r : Randomness) (values : ChainIndex → Digest) :
    IsTotalQueryBound (otsLeaf p lay key msg r values : OracleComp LeanXmss.HashSpec (Option Digest))
      (1 + (numChains * (chainLength - 1) + (1 + 0))) := by
  unfold otsLeaf
  refine isTotalQueryBound_bind (tweakableHash_isTotalQueryBound _ _ _) fun d ↦ ?_
  split
  · refine isTotalQueryBound_bind (isTotalQueryBound_sequenceFin (chainLength - 1) _ fun i ↦ ?_)
      fun _ ↦ isTotalQueryBound_bind (tweakableHash_isTotalQueryBound _ _ _) fun _ ↦ trivial
    exact (chainWalk_isTotalQueryBound _ _ _ _ _ _ _).mono (Nat.sub_le_sub_left (Nat.zero_le _) _)
  · trivial

/-- A tree fold of `levels` levels makes at most `levels` queries. -/
theorem treeFold_isTotalQueryBound (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) :
    ∀ (levels : ℕ) (v : Digest),
      IsTotalQueryBound (treeFold p lay key path levels v : OracleComp LeanXmss.HashSpec Digest) levels
  | 0, _ => trivial
  | levels + 1, v => by
    simp only [treeFold]
    refine isTotalQueryBound_bind (treeFold_isTotalQueryBound p lay key path levels v) fun _ ↦ ?_
    split <;> exact tweakableHash_isTotalQueryBound _ _ _

/-- A layer's root makes at most the leaf's and the path's queries. -/
theorem layerRoot_isTotalQueryBound (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (msg : HashInput) (part : LayerSignature) :
    IsTotalQueryBound (layerRoot p lay key msg part : OracleComp LeanXmss.HashSpec (Option Digest))
      ((1 + (numChains * (chainLength - 1) + (1 + 0))) + (layerHeight + 0)) := by
  unfold layerRoot
  refine isTotalQueryBound_bind (otsLeaf_isTotalQueryBound _ _ _ _ _ _) fun o ↦ ?_
  rcases o with _ | leaf
  · trivial
  · dsimp only
    have h1 : IsTotalQueryBound (treeFold p lay key part.path layerHeight leaf :
        OracleComp LeanXmss.HashSpec Digest) layerHeight :=
      treeFold_isTotalQueryBound p lay key part.path _ leaf
    generalize (treeFold p lay key part.path layerHeight leaf :
      OracleComp LeanXmss.HashSpec Digest) = X at h1 ⊢
    exact isTotalQueryBound_bind h1 fun r ↦ isQueryBound_pure (some r) 0 _ _

/-- **leanXMSS's verification makes at most `xmssVerifyBound` hash queries.** -/
theorem verify_isTotalQueryBound (pk : PublicKey) (msg : Message) (σ : Signature) :
    IsTotalQueryBound (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool)
      xmssVerifyBound := by
  simp only [Concrete.verify]
  have hb := layerRoot_isTotalQueryBound pk.parameter bottomLayer (keyAt σ.leafIndex bottomLayer)
    (bytesLE 32 msg) (σ.layers bottomLayer)
  generalize (layerRoot pk.parameter bottomLayer (keyAt σ.leafIndex bottomLayer) (bytesLE 32 msg)
    (σ.layers bottomLayer) : OracleComp LeanXmss.HashSpec (Option Digest)) = X at hb ⊢
  refine (isTotalQueryBound_bind (n₂ := (1 + (numChains * (chainLength - 1) + (1 + 0))) +
    (layerHeight + 0) + 0) hb fun o ↦ ?_).mono
    (show _ ≤ xmssVerifyBound by unfold xmssVerifyBound; omega)
  rcases o with _ | b
  · exact isQueryBound_pure _ _ _ _
  · dsimp only
    have ht := layerRoot_isTotalQueryBound pk.parameter topLayer (keyAt σ.leafIndex topLayer)
      (bytesLE 16 b) (σ.layers topLayer)
    generalize (layerRoot pk.parameter topLayer (keyAt σ.leafIndex topLayer) (bytesLE 16 b)
      (σ.layers topLayer) : OracleComp LeanXmss.HashSpec (Option Digest)) = Y at ht ⊢
    refine isTotalQueryBound_bind (n₂ := 0) ht fun o' ↦ ?_
    rcases o' with _ | r <;> exact isQueryBound_pure _ _ _ _

end
end LeanVM.E2E
