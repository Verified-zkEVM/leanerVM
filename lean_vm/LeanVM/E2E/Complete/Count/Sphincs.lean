/-
  LeanVM.E2E.Complete.Count.Sphincs

  The block prefixes a held leanSPHINCS signature's verification logs (L17, package B2): at most
  `686` queries, each of at most `1056` bytes.
-/

module

public import LeanVM.E2E.Complete.Count.Basic
public import LeanVM.E2E.Reduction.SphincsBound

/-!
# A leanSPHINCS verification logs at most `sphincsVerifyBlocks` block prefixes

Every query of `Sphincs.Concrete.verify` is `P || A || payload`: `16` bytes of parameter, `16` of
address, and a payload of at most `64 · 16 = 1024` bytes (the one-time leaf's `64` chain ends; the
forest's roots hash `256`, a child leaf `96`, a super-child `64`, a tree node `32`, the encoding
`20`, a chain step `16` and the message digest `48`). So every query is at most `1056` bytes
(`sphincsVerify_allQueriesSatisfy`), `16` block prefixes, and with at most
`sphincsVerifyBound = 686` queries (`sphincsVerify_isTotalQueryBound`) the logged run has at most
`686 · 16 = 10976` (`prefixCount_sphincsVerifyWith_le`, `sphincsVerifyBlocks_le`).
-/

namespace LeanVM.E2E.Complete

open OracleSpec OracleComp

@[expose] public section

/-- The longest query of leanSPHINCS's verification: the parameter, the address and the one-time
leaf's `64` chain ends. -/
def sphincsQueryLen : ℕ := 16 + 16 + _root_.Sphincs.numChains * 16

section Queries

open _root_.Sphincs _root_.Sphincs.Concrete

/-- The predicate on leanSPHINCS's queries: at most `sphincsQueryLen` bytes. -/
abbrev SphincsShortQuery (t : _root_.Sphincs.HashInput) : Prop := t.length ≤ sphincsQueryLen

/-- A flattening of parts of `k` elements each. -/
theorem sphincsCountFlatMap_length {α β : Type} (f : α → List β) (k : ℕ)
    (hf : ∀ a, (f a).length = k) : ∀ l : List α, (l.flatMap f).length = l.length * k
  | [] => by rw [List.flatMap_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, sphincsCountFlatMap_length f k hf l, hf a,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- `bytesLE 16` over `n` digests: `16 n` bytes. -/
theorem sphincsCount_flatMap_bytesLE {n : ℕ} (v : Fin n → _root_.Sphincs.Digest) :
    ((List.ofFn v).flatMap (bytesLE 16)).length = n * 16 :=
  (sphincsCountFlatMap_length (bytesLE 16) 16
    (fun _ ↦ by simp only [bytesLE, List.length_ofFn]) (List.ofFn _)).trans
      (congrArg (· * 16) List.length_ofFn)

/-- An oracle call on a short input asks a short query. -/
theorem sphincsCount_oracleHash (x : _root_.Sphincs.HashInput) (hx : SphincsShortQuery x) :
    AllQueriesSatisfy (oracleHash x : OracleComp _root_.Sphincs.HashSpec _root_.Sphincs.HashOutput)
      SphincsShortQuery := by
  change AllQueriesSatisfy ((liftM (_root_.Sphincs.HashSpec.query x) :
    OracleComp _root_.Sphincs.HashSpec _) >>= fun o ↦ pure o) _
  exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hx, fun _ ↦ allQueriesSatisfy_pure _ _⟩

/-- A tweakable hash with a payload of at most `1024` bytes asks a short query. -/
theorem sphincsCount_tweakableHash (p : _root_.Sphincs.PublicParameter)
    (d : _root_.Sphincs.HashDomain) (x : _root_.Sphincs.HashInput)
    (hx : x.length ≤ _root_.Sphincs.numChains * 16) :
    AllQueriesSatisfy (tweakableHash p d x : OracleComp _root_.Sphincs.HashSpec _root_.Sphincs.Digest)
      SphincsShortQuery := by
  refine allQueriesSatisfy_bind (sphincsCount_oracleHash _ ?_) fun _ ↦ allQueriesSatisfy_pure _ _
  simp only [SphincsShortQuery, tweakableHashInput, tweakBytes, fieldBytes, List.length_append,
    bytesLE, List.length_ofFn, sphincsQueryLen]
  omega

/-- A sequence of computations, each asking only `P`-queries. -/
theorem sphincsCount_sequenceFin {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : ι → Prop} : ∀ {n : ℕ} (c : Fin n → OracleComp spec α), (∀ i, AllQueriesSatisfy (c i) P) →
      AllQueriesSatisfy (_root_.Sphincs.Concrete.sequenceFin c) P
  | 0, _, _ => allQueriesSatisfy_pure _ _
  | n + 1, c, h => by
    simp only [_root_.Sphincs.Concrete.sequenceFin]
    exact allQueriesSatisfy_bind (h 0) fun _ ↦
      allQueriesSatisfy_bind (sphincsCount_sequenceFin (fun i ↦ c i.succ) fun i ↦ h i.succ)
        fun _ ↦ allQueriesSatisfy_pure _ _

theorem sphincsCount_chainWalk (p : _root_.Sphincs.PublicParameter) (lay : _root_.Sphincs.Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (c : _root_.Sphincs.ChainIndex) (start : ℕ) :
    ∀ (steps : ℕ) (v : _root_.Sphincs.Digest), AllQueriesSatisfy
      (chainWalk p lay tree leaf c start steps v :
        OracleComp _root_.Sphincs.HashSpec _root_.Sphincs.Digest) SphincsShortQuery
  | 0, _ => allQueriesSatisfy_pure _ _
  | steps + 1, v => by
    simp only [chainWalk]
    refine allQueriesSatisfy_bind (sphincsCount_chainWalk p lay tree leaf c start steps v)
      fun _ ↦ ?_
    split
    · refine sphincsCount_tweakableHash _ _ _ ?_
      simp only [bytesLE, List.length_ofFn, _root_.Sphincs.numChains]
      omega
    · exact allQueriesSatisfy_pure _ _

theorem sphincsCount_forestWalk (p : _root_.Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (start : ℕ) :
    ∀ (steps : ℕ) (v : _root_.Sphincs.Digest), AllQueriesSatisfy
      (forestWalk p index c s j a i start steps v :
        OracleComp _root_.Sphincs.HashSpec _root_.Sphincs.Digest) SphincsShortQuery
  | 0, _ => allQueriesSatisfy_pure _ _
  | steps + 1, v => by
    simp only [forestWalk]
    refine allQueriesSatisfy_bind (sphincsCount_forestWalk p index c s j a i start steps v)
      fun _ ↦ ?_
    split
    · refine sphincsCount_tweakableHash _ _ _ ?_
      simp only [bytesLE, List.length_ofFn, _root_.Sphincs.numChains]
      omega
    · exact allQueriesSatisfy_pure _ _

theorem sphincsCount_nodePayload (l r : _root_.Sphincs.Digest) :
    (nodePayload l r).length ≤ _root_.Sphincs.numChains * 16 := by
  simp only [nodePayload, List.length_append, bytesLE, List.length_ofFn, _root_.Sphincs.numChains]
  omega

theorem sphincsCount_treeFold (p : _root_.Sphincs.PublicParameter) (lay : _root_.Sphincs.Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (path : ℕ → _root_.Sphincs.Digest) :
    ∀ (levels : ℕ) (v : _root_.Sphincs.Digest), AllQueriesSatisfy
      (treeFold p lay tree leaf path levels v :
        OracleComp _root_.Sphincs.HashSpec _root_.Sphincs.Digest) SphincsShortQuery
  | 0, _ => allQueriesSatisfy_pure _ _
  | levels + 1, v => by
    simp only [treeFold]
    refine allQueriesSatisfy_bind (sphincsCount_treeFold p lay tree leaf path levels v) fun _ ↦ ?_
    split <;> exact sphincsCount_tweakableHash _ _ _ (sphincsCount_nodePayload _ _)

theorem sphincsCount_subFold (p : _root_.Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (path : Fin subHeight → _root_.Sphincs.Digest) :
    ∀ (levels : ℕ) (v : _root_.Sphincs.Digest), AllQueriesSatisfy
      (subFold p index c s j a path levels v :
        OracleComp _root_.Sphincs.HashSpec _root_.Sphincs.Digest) SphincsShortQuery
  | 0, _ => allQueriesSatisfy_pure _ _
  | levels + 1, v => by
    simp only [subFold]
    refine allQueriesSatisfy_bind (sphincsCount_subFold p index c s j a path levels v) fun _ ↦ ?_
    split
    · split <;> exact sphincsCount_tweakableHash _ _ _ (sphincsCount_nodePayload _ _)
    · exact allQueriesSatisfy_pure _ _

theorem sphincsCount_topFold (p : _root_.Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (path : Fin topHeight → _root_.Sphincs.Digest) :
    ∀ (levels : ℕ) (v : _root_.Sphincs.Digest), AllQueriesSatisfy
      (topFold p index c s path levels v :
        OracleComp _root_.Sphincs.HashSpec _root_.Sphincs.Digest) SphincsShortQuery
  | 0, _ => allQueriesSatisfy_pure _ _
  | levels + 1, v => by
    simp only [topFold]
    refine allQueriesSatisfy_bind (sphincsCount_topFold p index c s path levels v) fun _ ↦ ?_
    split
    · split <;> exact sphincsCount_tweakableHash _ _ _ (sphincsCount_nodePayload _ _)
    · exact allQueriesSatisfy_pure _ _

theorem sphincsCount_childRecover (p : _root_.Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (word : Codeword)
    (values : FChain → _root_.Sphincs.Digest) :
    AllQueriesSatisfy (childRecover p index c s j a word values :
      OracleComp _root_.Sphincs.HashSpec _root_.Sphincs.Digest) SphincsShortQuery := by
  unfold childRecover
  refine allQueriesSatisfy_bind (sphincsCount_sequenceFin _ fun i ↦
    sphincsCount_forestWalk _ _ _ _ _ _ _ _ _ _) fun _ ↦ sphincsCount_tweakableHash _ _ _ ?_
  rw [childPayload, sphincsCount_flatMap_bytesLE]
  simp only [childChains, _root_.Sphincs.numChains]
  omega

theorem sphincsCount_coordRecover (p : _root_.Sphincs.PublicParameter) (index : Index) (c : Coord)
    (mark : CoordMark) (opening : CoordOpening) :
    AllQueriesSatisfy (coordRecover p index c mark opening :
      OracleComp _root_.Sphincs.HashSpec (_root_.Sphincs.Digest × _root_.Sphincs.Digest))
      SphincsShortQuery := by
  unfold coordRecover
  refine allQueriesSatisfy_bind (sphincsCount_sequenceFin _ fun j ↦
    allQueriesSatisfy_bind (sphincsCount_childRecover _ _ _ _ _ _ _ _) fun _ ↦
      allQueriesSatisfy_bind (sphincsCount_subFold _ _ _ _ _ _ _ _ _) fun _ ↦
        allQueriesSatisfy_pure _ _) fun _ ↦
    allQueriesSatisfy_bind (sphincsCount_tweakableHash _ _ _ ?_) fun _ ↦
      allQueriesSatisfy_bind (sphincsCount_topFold _ _ _ _ _ _ _) fun _ ↦
        allQueriesSatisfy_pure _ _
  simp only [superPayload, nodePayload, List.length_append, bytesLE, List.length_ofFn,
    _root_.Sphincs.numChains]
  omega

theorem sphincsCount_forestRecover (p : _root_.Sphincs.PublicParameter) (index : Index)
    (marks : Coord → CoordMark) (opening : Coord → CoordOpening) :
    AllQueriesSatisfy (forestRecover p index marks opening :
      OracleComp _root_.Sphincs.HashSpec _root_.Sphincs.Digest) SphincsShortQuery := by
  unfold forestRecover
  refine allQueriesSatisfy_bind (sphincsCount_sequenceFin _ fun _ ↦
    sphincsCount_coordRecover _ _ _ _ _) fun tops ↦ sphincsCount_tweakableHash _ _ _ ?_
  rw [rootsPayload, sphincsCountFlatMap_length _ 32 (fun pair ↦ by
    simp only [nodePayload, List.length_append, bytesLE, List.length_ofFn]), List.length_ofFn]
  simp only [forestCoords, _root_.Sphincs.numChains]
  omega

theorem sphincsCount_otsLeaf (p : _root_.Sphincs.PublicParameter) (lay : _root_.Sphincs.Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (msg : _root_.Sphincs.Digest) (counter : Counter)
    (values : _root_.Sphincs.ChainIndex → _root_.Sphincs.Digest) :
    AllQueriesSatisfy (otsLeaf p lay tree leaf msg counter values :
      OracleComp _root_.Sphincs.HashSpec (Option _root_.Sphincs.Digest)) SphincsShortQuery := by
  unfold otsLeaf encode
  rw [bind_assoc]
  refine allQueriesSatisfy_bind (sphincsCount_tweakableHash _ _ _ ?_) fun _ ↦ ?_
  · simp only [List.length_append, bytesLE, List.length_ofFn, _root_.Sphincs.numChains]
    omega
  rw [pure_bind]
  split
  · refine allQueriesSatisfy_bind (sphincsCount_sequenceFin _ fun i ↦
      sphincsCount_chainWalk _ _ _ _ _ _ _ _) fun _ ↦
        allQueriesSatisfy_bind (sphincsCount_tweakableHash _ _ _ ?_) fun _ ↦
          allQueriesSatisfy_pure _ _
    rw [leafPayload, sphincsCount_flatMap_bytesLE]
  · exact allQueriesSatisfy_pure _ _

theorem sphincsCount_verifyLayers (p : _root_.Sphincs.PublicParameter) (index : Index)
    (σ : _root_.Sphincs.Signature) (remaining : ℕ) (msg : _root_.Sphincs.Digest) :
    AllQueriesSatisfy (verifyLayers p index σ remaining msg :
      OracleComp _root_.Sphincs.HashSpec (Option _root_.Sphincs.Digest)) SphincsShortQuery := by
  induction remaining generalizing msg with
  | zero => exact allQueriesSatisfy_pure _ _
  | succ remaining ih =>
    simp only [verifyLayers]
    split
    · refine allQueriesSatisfy_bind (sphincsCount_otsLeaf _ _ _ _ _ _ _) fun o ↦ ?_
      rcases o with _ | v
      · exact allQueriesSatisfy_pure _ _
      · exact allQueriesSatisfy_bind (sphincsCount_treeFold _ _ _ _ _ _ _) fun _ ↦ ih _
    · exact allQueriesSatisfy_pure _ _

/-- **Every query of leanSPHINCS's verification is at most `sphincsQueryLen = 1056` bytes.** -/
theorem sphincsVerify_allQueriesSatisfy (pk : _root_.Sphincs.PublicKey)
    (msg : _root_.Sphincs.Message) (σ : _root_.Sphincs.Signature) :
    AllQueriesSatisfy (_root_.Sphincs.Concrete.verify pk msg σ :
      OracleComp _root_.Sphincs.HashSpec Bool) SphincsShortQuery := by
  simp only [Concrete.verify, messageDigest, messageDigestCall, bind_assoc, pure_bind]
  refine allQueriesSatisfy_bind (sphincsCount_oracleHash _ ?_) fun _ ↦
    allQueriesSatisfy_bind (sphincsCount_forestRecover _ _ _ _) fun _ ↦
      allQueriesSatisfy_bind (sphincsCount_verifyLayers _ _ _ _ _) fun o ↦ ?_
  · simp only [SphincsShortQuery, tweakableHashInput, tweakBytes, fieldBytes,
      messageDigestPayload, List.length_append, bytesLE, List.length_ofFn, sphincsQueryLen,
      _root_.Sphincs.numChains]
    omega
  · rcases o with _ | r <;> exact allQueriesSatisfy_pure _ _

end Queries

/-! ## The count -/

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash

/-- The block prefixes of a leanSPHINCS verification's log: `686` queries of at most `16` each. -/
def sphincsVerifyBlocks : ℕ := sphincsVerifyBound * 16

/-- **A held leanSPHINCS signature's verification logs at most `sphincsVerifyBlocks` block
prefixes**, whatever the key, the message and the signature. -/
theorem prefixCount_sphincsVerifyWith_le (H : Bytes → Digest) (pk : _root_.Sphincs.PublicKey)
    (msg : _root_.Sphincs.Message) (σ : _root_.Sphincs.Signature) :
    prefixCount (Node.sphincsVerifyWith (LogM.hash H) pk msg σ).log ≤ sphincsVerifyBlocks := by
  rw [sphincsVerifyWith_eq_simulateQ]
  refine prefixCount_simulateQ_le H Node.digestBits _ _ (sphincsVerify_isTotalQueryBound pk msg σ)
    ((sphincsVerify_allQueriesSatisfy pk msg σ).mono fun t ht ↦ nBlocks_le_of_length_le ?_)
  exact ht.trans (by decide)

theorem sphincsVerifyBlocks_le : sphincsVerifyBlocks ≤ 2 ^ 20 := by decide

end
end LeanVM.E2E.Complete
