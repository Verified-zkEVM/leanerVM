/-
  LeanVM.E2E.Complete.Count.Xmss

  The block prefixes a held leanXMSS signature's verification logs (L17, package B1): at most
  `384` queries, each of at most `960` bytes.
-/

module

public import LeanVM.E2E.Complete.Count.Basic
public import LeanVM.E2E.Reduction.VerifyBound

/-!
# A leanXMSS verification logs at most `xmssVerifyBlocks` block prefixes

Every query of `LeanXmss.Concrete.verify` is a tweakable hash's input `P || A || payload`: `16`
bytes of parameter, `16` of address, and a payload of at most `58 · 16 = 928` bytes (the leaf's
`58` chain ends; a chain step and a tree node hash `32`, the message digest `48`). So every query
is at most `960` bytes (`xmssVerify_allQueriesSatisfy`), `14` block prefixes, and with at most
`xmssVerifyBound = 384` queries (`verify_isTotalQueryBound`) the logged run has at most
`384 · 14 = 5376` (`prefixCount_xmssVerifyWith_le`, `xmssVerifyBlocks_le`).
-/

namespace LeanVM.E2E.Complete

open OracleSpec OracleComp

@[expose] public section

/-- The longest query of leanXMSS's verification: the parameter, the address and the leaf's `58`
chain ends. -/
def xmssQueryLen : ℕ := 16 + 16 + LeanXmss.numChains * 16

section Queries

open LeanXmss LeanXmss.Concrete

/-- The predicate on leanXMSS's queries: at most `xmssQueryLen` bytes. -/
abbrev XmssShortQuery (t : HashInput) : Prop := t.length ≤ xmssQueryLen

/-- A flattening of parts of `k` elements each. -/
theorem xmssCountFlatMap_length {α β : Type} (f : α → List β) (k : ℕ) (hf : ∀ a, (f a).length = k) :
    ∀ l : List α, (l.flatMap f).length = l.length * k
  | [] => by rw [List.flatMap_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, xmssCountFlatMap_length f k hf l, hf a,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- A tweakable hash with a payload of at most `928` bytes asks a short query. -/
theorem xmssCount_tweakableHash (p : PublicParameter) (d : HashDomain) (x : HashInput)
    (hx : x.length ≤ numChains * 16) :
    AllQueriesSatisfy (tweakableHash p d x : OracleComp LeanXmss.HashSpec LeanXmss.Digest)
      XmssShortQuery := by
  simp only [tweakableHash, oracleHash]
  change AllQueriesSatisfy ((liftM (LeanXmss.HashSpec.query (tweakableHashInput p d x)) :
    OracleComp LeanXmss.HashSpec _) >>= fun o ↦ pure (truncateHash o)) _
  refine (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨?_, fun _ ↦ allQueriesSatisfy_pure _ _⟩
  simp only [XmssShortQuery, tweakableHashInput, tweakBytes, fieldBytes, List.length_append,
    bytesLE, List.length_ofFn, xmssQueryLen]
  omega

/-- A sequence of computations, each asking only `P`-queries. -/
theorem xmssCount_sequenceFin {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} {P : ι → Prop} :
    ∀ {n : ℕ} (c : Fin n → OracleComp spec α), (∀ i, AllQueriesSatisfy (c i) P) →
      AllQueriesSatisfy (LeanXmss.Concrete.sequenceFin c) P
  | 0, _, _ => allQueriesSatisfy_pure _ _
  | n + 1, c, h => by
    simp only [LeanXmss.Concrete.sequenceFin]
    exact allQueriesSatisfy_bind (h 0) fun _ ↦
      allQueriesSatisfy_bind (xmssCount_sequenceFin (fun i ↦ c i.succ) fun i ↦ h i.succ)
        fun _ ↦ allQueriesSatisfy_pure _ _

theorem xmssCount_chainWalk (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (c : ChainIndex) (start : ℕ) :
    ∀ (steps : ℕ) (v : LeanXmss.Digest),
      AllQueriesSatisfy (chainWalk p lay key c start steps v :
        OracleComp LeanXmss.HashSpec LeanXmss.Digest) XmssShortQuery
  | 0, _ => allQueriesSatisfy_pure _ _
  | steps + 1, v => by
    simp only [chainWalk]
    refine allQueriesSatisfy_bind (xmssCount_chainWalk p lay key c start steps v) fun _ ↦ ?_
    split
    · refine xmssCount_tweakableHash _ _ _ ?_
      simp only [chainPayload, List.length_append, bytesLE, List.length_ofFn, numChains]
      omega
    · exact allQueriesSatisfy_pure _ _

theorem xmssCount_otsLeaf (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (msg : HashInput) (hm : msg.length ≤ 32) (r : Randomness) (values : ChainIndex → LeanXmss.Digest) :
    AllQueriesSatisfy (otsLeaf p lay key msg r values :
      OracleComp LeanXmss.HashSpec (Option LeanXmss.Digest)) XmssShortQuery := by
  unfold otsLeaf
  refine allQueriesSatisfy_bind (xmssCount_tweakableHash _ _ _ ?_) fun d ↦ ?_
  · simp only [List.length_append, bytesLE, List.length_ofFn, numChains]
    omega
  split
  · refine allQueriesSatisfy_bind (xmssCount_sequenceFin _ fun i ↦ xmssCount_chainWalk _ _ _ _ _ _ _)
      fun _ ↦ allQueriesSatisfy_bind (xmssCount_tweakableHash _ _ _ ?_) fun _ ↦
        allQueriesSatisfy_pure _ _
    exact le_of_eq ((xmssCountFlatMap_length (bytesLE 16) 16
      (fun _ ↦ by simp only [bytesLE, List.length_ofFn]) (List.ofFn _)).trans
        (congrArg (· * 16) List.length_ofFn))
  · exact allQueriesSatisfy_pure _ _

theorem xmssCount_treeFold (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → LeanXmss.Digest) :
    ∀ (levels : ℕ) (v : LeanXmss.Digest),
      AllQueriesSatisfy (treeFold p lay key path levels v :
        OracleComp LeanXmss.HashSpec LeanXmss.Digest) XmssShortQuery
  | 0, _ => allQueriesSatisfy_pure _ _
  | levels + 1, v => by
    simp only [treeFold]
    refine allQueriesSatisfy_bind (xmssCount_treeFold p lay key path levels v) fun _ ↦ ?_
    split <;>
    · refine xmssCount_tweakableHash _ _ _ ?_
      simp only [nodePayload, List.length_append, bytesLE, List.length_ofFn, numChains]
      omega

theorem xmssCount_layerRoot (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (msg : HashInput) (hm : msg.length ≤ 32) (part : LayerSignature) :
    AllQueriesSatisfy (layerRoot p lay key msg part :
      OracleComp LeanXmss.HashSpec (Option LeanXmss.Digest)) XmssShortQuery := by
  unfold layerRoot
  refine allQueriesSatisfy_bind (xmssCount_otsLeaf _ _ _ _ hm _ _) fun o ↦ ?_
  rcases o with _ | leaf
  · exact allQueriesSatisfy_pure _ _
  · dsimp only
    have h1 := xmssCount_treeFold p lay key part.path layerHeight leaf
    generalize (treeFold p lay key part.path layerHeight leaf :
      OracleComp LeanXmss.HashSpec LeanXmss.Digest) = X at h1 ⊢
    exact allQueriesSatisfy_bind h1 fun _ ↦ allQueriesSatisfy_pure _ _

/-- **Every query of leanXMSS's verification is at most `xmssQueryLen = 960` bytes.** -/
theorem xmssVerify_allQueriesSatisfy (pk : PublicKey) (msg : Message) (σ : Signature) :
    AllQueriesSatisfy (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool)
      XmssShortQuery := by
  simp only [Concrete.verify]
  have hb := xmssCount_layerRoot pk.parameter bottomLayer (keyAt σ.leafIndex bottomLayer)
    (bytesLE 32 msg) (by simp only [bytesLE, List.length_ofFn, le_refl]) (σ.layers bottomLayer)
  generalize (layerRoot pk.parameter bottomLayer (keyAt σ.leafIndex bottomLayer) (bytesLE 32 msg)
    (σ.layers bottomLayer) : OracleComp LeanXmss.HashSpec (Option LeanXmss.Digest)) = X at hb ⊢
  refine allQueriesSatisfy_bind hb fun o ↦ ?_
  rcases o with _ | b
  · exact allQueriesSatisfy_pure _ _
  · dsimp only
    have ht := xmssCount_layerRoot pk.parameter topLayer (keyAt σ.leafIndex topLayer)
      (bytesLE 16 b) (by simp only [bytesLE, List.length_ofFn]; omega) (σ.layers topLayer)
    generalize (layerRoot pk.parameter topLayer (keyAt σ.leafIndex topLayer) (bytesLE 16 b)
      (σ.layers topLayer) : OracleComp LeanXmss.HashSpec (Option LeanXmss.Digest)) = Y at ht ⊢
    refine allQueriesSatisfy_bind ht fun o' ↦ ?_
    rcases o' with _ | r <;> exact allQueriesSatisfy_pure _ _

end Queries

/-! ## The count -/

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash

/-- The block prefixes of a leanXMSS verification's log: `384` queries of at most `14` each. -/
def xmssVerifyBlocks : ℕ := xmssVerifyBound * 14

/-- **A held leanXMSS signature's verification logs at most `xmssVerifyBlocks` block
prefixes**, whatever the key, the message and the signature. -/
theorem prefixCount_xmssVerifyWith_le (H : Bytes → Digest) (pk : LeanXmss.PublicKey)
    (msg : LeanXmss.Message) (σ : LeanXmss.Signature) :
    prefixCount (Node.xmssVerifyWith (LogM.hash H) pk msg σ).log ≤ xmssVerifyBlocks := by
  rw [xmssVerifyWith_eq_simulateQ]
  refine prefixCount_simulateQ_le H Node.digestBits _ _ (verify_isTotalQueryBound pk msg σ)
    ((xmssVerify_allQueriesSatisfy pk msg σ).mono fun t ht ↦ nBlocks_le_of_length_le ?_)
  exact ht.trans (by decide)

theorem xmssVerifyBlocks_le : xmssVerifyBlocks ≤ 2 ^ 20 := by decide

end
end LeanVM.E2E.Complete
