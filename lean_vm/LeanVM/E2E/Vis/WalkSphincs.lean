/-
  LeanVM.E2E.Vis.WalkSphincs

  W-vis, P2c: every hash query of leanSPHINCS's key generation, signer and verifier is a scheme
  input of the key's parameter (`P ‖ A ‖ payload`, at least 48 bytes) or one of key generation's
  two derivations.
-/

module

public import LeanVM.E2E.Vis.WalkXmss

/-!
# leanSPHINCS's queries (W-vis, P2c)

The leanSPHINCS counterpart of `Vis/WalkXmss.lean`. Every leanSPHINCS hash input is
`P ‖ A ‖ payload` (`tweakableHashInput`, `keygenHashInput`, `randomizerHashInput`) with a payload
of at least 16 bytes (a chain step's `16`, the encoding's `20`, a node's `32`, …), and no address
of `A_param`'s type `5`; the exceptions are key generation's `"leanSPHINCS" ‖ S0` and
`0^16 ‖ A_param ‖ S`.

* `sphincs_sign_queries`, `sphincs_verify_queries` (and the `…N` forms, not shaped as a
  derivation): the signer's and the verifier's queries are scheme inputs of the key's parameter.
* `sphincs_keygen_queries` (`…N`), `sphincs_keygen_param`, `sphincs_keygen_deriv_count`: as for
  leanXMSS, through the forest-free key generation (the kept subtree, its spine and the
  surrogates).

The walks follow `Reduction/SphincsBound.lean`.
-/

namespace LeanVM.E2E

open OracleSpec OracleComp _root_.Sphincs _root_.Sphincs.Concrete

@[expose] public section

/-! ## Addresses -/

/-- A leanSPHINCS address is an address. -/
theorem sphincs_addrOK (f : TweakFields) : AddrOK (fieldBytes f) := by
  refine ⟨by simp [fieldBytes, bytesLE], ?_⟩
  have h : (fieldBytes f).drop 8 = bytesLE 8 0 := by
    rw [show fieldBytes f = (bytesLE 4 f.lo ++ bytesLE 3 f.hi ++ bytesLE 1 (f.step ++ f.tag)) ++
      bytesLE 8 0 from rfl, List.drop_left' (by simp [bytesLE])]
  rw [h]
  decide

/-- A leanSPHINCS address of another type than `A_param`'s. -/
theorem sphincs_fieldBytes_ne (f : TweakFields) (h : f.tag ≠ 5#5) :
    fieldBytes f ≠ paramPrefix.drop 16 :=
  ne_paramAddr_of_byte7 h (s := f.step) rfl

/-- A leanSPHINCS input `P ‖ A ‖ payload`, `A` of another type than `A_param`'s. -/
theorem sphincs_schemeInputN (p : Sphincs.PublicParameter) (f : TweakFields) (r : Sphincs.HashInput)
    (hf : f.tag ≠ 5#5) (hr : 16 ≤ r.length) :
    SchemeInputN (bytesLE 16 p) (bytesLE 16 p ++ fieldBytes f ++ r) :=
  schemeInputN_append (by simp [bytesLE]) (sphincs_addrOK f) (sphincs_fieldBytes_ne f hf) hr

/-- No verification address has `A_param`'s type. -/
theorem sphincs_hashDomain_tag (d : HashDomain) : (hashDomainFields d).tag ≠ 5#5 := by
  cases d <;> (simp only [hashDomainFields, tweakFields]; decide)

/-- No derivation but the parameter's has `A_param`'s type. -/
theorem sphincs_keygenDomain_tag (d : KeygenDomain) (hd : d ≠ .parameter) :
    (keygenDomainFields d).tag ≠ 5#5 := by
  cases d
  · exact absurd rfl hd
  all_goals (simp only [keygenDomainFields, tweakFields]; decide)

/-! ## The walks -/

/-- The walks' predicate. -/
abbrev WalkSQ (p : Sphincs.PublicParameter) : Sphincs.HashInput → Prop :=
  SchemeInputN (bytesLE 16 p)

/-- One oracle call. -/
theorem walkS_oracleHash {P : Sphincs.HashInput → Prop} (x : Sphincs.HashInput) (hx : P x) :
    AllQueriesSatisfy (oracleHash x : OracleComp Sphincs.HashSpec Sphincs.HashOutput) P := by
  change AllQueriesSatisfy ((liftM (Sphincs.HashSpec.query x) : OracleComp Sphincs.HashSpec _) >>=
    fun o ↦ pure o) P
  exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hx, fun _ ↦ allQueriesSatisfy_pure _ _⟩

/-- A tweakable hash with a payload of at least 16 bytes. -/
theorem walkS_tweakableHash (p : Sphincs.PublicParameter) (d : HashDomain) (x : Sphincs.HashInput)
    (hx : 16 ≤ x.length) :
    AllQueriesSatisfy (tweakableHash p d x : OracleComp Sphincs.HashSpec Sphincs.Digest)
      (WalkSQ p) :=
  allQueriesSatisfy_bind
    (walkS_oracleHash _ (sphincs_schemeInputN p _ x (sphincs_hashDomain_tag d) hx))
    fun _ ↦ allQueriesSatisfy_pure _ _

/-- A seed derivation other than the parameter's. -/
theorem walkS_derive (p : Sphincs.PublicParameter) (d : KeygenDomain) (hd : d ≠ .parameter)
    (seed : Sphincs.MasterSeed) :
    AllQueriesSatisfy (oracleHash (keygenHashInput p d seed) :
      OracleComp Sphincs.HashSpec Sphincs.HashOutput) (WalkSQ p) :=
  walkS_oracleHash _
    (sphincs_schemeInputN p _ _ (sphincs_keygenDomain_tag d hd) (by simp [bytesLE]))

/-- A sequence of computations, each asking only `P`-queries. -/
theorem walkS_sequenceFin {α : Type} {P : Sphincs.HashInput → Prop} :
    ∀ {n : ℕ} (c : Fin n → OracleComp Sphincs.HashSpec α), (∀ i, AllQueriesSatisfy (c i) P) →
      AllQueriesSatisfy (sequenceFin c) P
  | 0, _, _ => allQueriesSatisfy_pure _ _
  | n + 1, c, h => by
    simp only [sequenceFin]
    exact allQueriesSatisfy_bind (h 0) fun _ ↦
      allQueriesSatisfy_bind (walkS_sequenceFin (fun i ↦ c i.succ) fun i ↦ h i.succ)
        fun _ ↦ allQueriesSatisfy_pure _ _

/-- A flattening of `n + 1` parts of at least 16 bytes each. -/
theorem walkS_flatMap_length {β : Type} {n : ℕ} (v : Fin (n + 1) → β) (g : β → List UInt8)
    (hg : ∀ b, 16 ≤ (g b).length) : 16 ≤ ((List.ofFn v).flatMap g).length := by
  rw [List.ofFn_succ, List.flatMap_cons, List.length_append]
  have := hg (v 0)
  omega

theorem walkS_nodePayload (l r : Sphincs.Digest) : 16 ≤ (nodePayload l r).length := by
  simp [nodePayload, bytesLE]

theorem walkS_bytes16 (v : Sphincs.Digest) : 16 ≤ (bytesLE 16 v).length := by
  simp [bytesLE]

theorem walkS_chainWalk (p : Sphincs.PublicParameter) (lay : Sphincs.Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (c : Sphincs.ChainIndex) (start : ℕ) : ∀ (steps : ℕ) (v : Sphincs.Digest),
      AllQueriesSatisfy (chainWalk p lay tree leaf c start steps v :
        OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p)
  | 0, _ => allQueriesSatisfy_pure _ _
  | steps + 1, v => by
    simp only [chainWalk]
    refine allQueriesSatisfy_bind (walkS_chainWalk p lay tree leaf c start steps v) fun _ ↦ ?_
    split
    · exact walkS_tweakableHash _ _ _ (walkS_bytes16 _)
    · exact allQueriesSatisfy_pure _ _

theorem walkS_forestWalk (p : Sphincs.PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (i : FChain) (start : ℕ) : ∀ (steps : ℕ) (v : Sphincs.Digest),
      AllQueriesSatisfy (forestWalk p index c s j a i start steps v :
        OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p)
  | 0, _ => allQueriesSatisfy_pure _ _
  | steps + 1, v => by
    simp only [forestWalk]
    refine allQueriesSatisfy_bind (walkS_forestWalk p index c s j a i start steps v) fun _ ↦ ?_
    split
    · exact walkS_tweakableHash _ _ _ (walkS_bytes16 _)
    · exact allQueriesSatisfy_pure _ _

theorem walkS_leafHash (p : Sphincs.PublicParameter) (lay : Sphincs.Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (e : Sphincs.ChainIndex → Sphincs.Digest) :
    AllQueriesSatisfy (leafHash p lay tree leaf e : OracleComp Sphincs.HashSpec Sphincs.Digest)
      (WalkSQ p) :=
  walkS_tweakableHash _ _ _ (walkS_flatMap_length (n := 63) e _ walkS_bytes16)

theorem walkS_encode (p : Sphincs.PublicParameter) (lay : Sphincs.Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (msg : Sphincs.Digest) (counter : Counter) :
    AllQueriesSatisfy (encode p lay tree leaf msg counter : OracleComp Sphincs.HashSpec _)
      (WalkSQ p) :=
  allQueriesSatisfy_bind (walkS_tweakableHash _ _ _ (by simp [bytesLE])) fun _ ↦
    allQueriesSatisfy_pure _ _

/-! ### The tree -/

theorem walkS_otsSecrets (p : Sphincs.PublicParameter) (lay : Sphincs.Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : Sphincs.MasterSeed) :
    AllQueriesSatisfy (Seeded.otsSecrets p lay tree leaf seed :
      OracleComp Sphincs.HashSpec (Sphincs.ChainIndex → Sphincs.Digest)) (WalkSQ p) := by
  unfold Seeded.otsSecrets
  exact allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦ walkS_derive _ _ (by simp) _)
    fun _ ↦ allQueriesSatisfy_pure _ _

theorem walkS_chainWalks (p : Sphincs.PublicParameter) (lay : Sphincs.Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (steps : Sphincs.ChainIndex → ℕ)
    (secrets : Sphincs.ChainIndex → Sphincs.Digest) :
    AllQueriesSatisfy (sequenceFin fun chainIdx ↦ chainWalk p lay tree leaf chainIdx 0
      (steps chainIdx) (secrets chainIdx) :
        OracleComp Sphincs.HashSpec (Sphincs.ChainIndex → Sphincs.Digest)) (WalkSQ p) :=
  walkS_sequenceFin _ fun _ ↦ walkS_chainWalk _ _ _ _ _ _ _ _

theorem walkS_treeNode (p : Sphincs.PublicParameter) (lay : Sphincs.Layer) (tree : TreeIndex)
    (seed : Sphincs.MasterSeed) : ∀ (level node : ℕ),
      AllQueriesSatisfy (Seeded.treeNode p lay tree seed level node :
        OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p)
  | 0, node => by
    simp only [Seeded.treeNode, Seeded.oneTimePublicKey, bind_assoc]
    exact allQueriesSatisfy_bind (walkS_otsSecrets _ _ _ _ _) fun _ ↦
      allQueriesSatisfy_bind (walkS_chainWalks _ _ _ _ _ _) fun _ ↦ walkS_leafHash _ _ _ _ _
  | level + 1, node => by
    simp only [Seeded.treeNode]
    exact allQueriesSatisfy_bind (walkS_treeNode p lay tree seed level _) fun _ ↦
      allQueriesSatisfy_bind (walkS_treeNode p lay tree seed level _) fun _ ↦
        walkS_tweakableHash _ _ _ (walkS_nodePayload _ _)

theorem walkS_otsSignFrom (p : Sphincs.PublicParameter) (lay : Sphincs.Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : Sphincs.MasterSeed) (msg : Sphincs.Digest) :
    ∀ (attempts counter : ℕ), AllQueriesSatisfy (Seeded.otsSignFrom p lay tree leaf seed msg
      attempts counter : OracleComp Sphincs.HashSpec _) (WalkSQ p)
  | 0, _ => allQueriesSatisfy_pure _ _
  | attempts + 1, counter => by
    simp only [Seeded.otsSignFrom]
    refine allQueriesSatisfy_bind (walkS_encode _ _ _ _ _ _) fun o ↦ ?_
    rcases o with _ | e
    · exact walkS_otsSignFrom p lay tree leaf seed msg attempts (counter + 1)
    · exact allQueriesSatisfy_bind (walkS_otsSecrets _ _ _ _ _) fun _ ↦
        allQueriesSatisfy_bind (walkS_chainWalks _ _ _ _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _

/-! ### The forest -/

theorem walkS_forestSecrets (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (seed : Sphincs.MasterSeed) :
    AllQueriesSatisfy (Seeded.forestSecrets p index c s j a seed :
      OracleComp Sphincs.HashSpec (FChain → Sphincs.Digest)) (WalkSQ p) := by
  unfold Seeded.forestSecrets
  exact allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦ walkS_derive _ _ (by simp) _)
    fun _ ↦ allQueriesSatisfy_pure _ _

theorem walkS_subNode (p : Sphincs.PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (seed : Sphincs.MasterSeed) : ∀ (level node : ℕ),
      AllQueriesSatisfy (Seeded.subNode p index c s j seed level node :
        OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p)
  | 0, node => by
    simp only [Seeded.subNode, Seeded.childLeaf]
    exact allQueriesSatisfy_bind (walkS_forestSecrets _ _ _ _ _ _ _) fun _ ↦
      allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦ walkS_forestWalk _ _ _ _ _ _ _ _ _ _)
        fun e ↦ walkS_tweakableHash _ _ _ (walkS_flatMap_length (n := 5) e _ walkS_bytes16)
  | level + 1, node => by
    simp only [Seeded.subNode]
    refine allQueriesSatisfy_bind (walkS_subNode p index c s j seed level _) fun _ ↦
      allQueriesSatisfy_bind (walkS_subNode p index c s j seed level _) fun _ ↦ ?_
    split
    · exact walkS_tweakableHash _ _ _ (walkS_nodePayload _ _)
    · exact allQueriesSatisfy_pure _ _

theorem walkS_superNode (p : Sphincs.PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (seed : Sphincs.MasterSeed) :
    AllQueriesSatisfy (Seeded.superNode p index c s seed :
      OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p) := by
  unfold Seeded.superNode superHash
  refine allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦
    allQueriesSatisfy_bind (walkS_subNode _ _ _ _ _ _ _ _) fun _ ↦
      allQueriesSatisfy_bind (walkS_subNode _ _ _ _ _ _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _)
    fun _ ↦ walkS_tweakableHash _ _ _ ?_
  simp only [superPayload, List.length_append]
  have := walkS_nodePayload
  grind

theorem walkS_topNode (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (seed : Sphincs.MasterSeed) : ∀ (level node : ℕ),
      AllQueriesSatisfy (Seeded.topNode p index c seed level node :
        OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p)
  | 0, node => by
    simp only [Seeded.topNode]
    exact walkS_superNode _ _ _ _ _
  | level + 1, node => by
    simp only [Seeded.topNode]
    refine allQueriesSatisfy_bind (walkS_topNode p index c seed level _) fun _ ↦
      allQueriesSatisfy_bind (walkS_topNode p index c seed level _) fun _ ↦ ?_
    split
    · exact walkS_tweakableHash _ _ _ (walkS_nodePayload _ _)
    · exact allQueriesSatisfy_pure _ _

theorem walkS_rootsPayload (tops : Coord → Sphincs.Digest × Sphincs.Digest) :
    16 ≤ (rootsPayload tops).length :=
  walkS_flatMap_length (n := 7) tops _ fun _ ↦ walkS_nodePayload _ _

theorem walkS_forestKey (p : Sphincs.PublicParameter) (index : Index) (seed : Sphincs.MasterSeed) :
    AllQueriesSatisfy (Seeded.forestKey p index seed :
      OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p) := by
  unfold Seeded.forestKey
  exact allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦
    allQueriesSatisfy_bind (walkS_topNode _ _ _ _ _ _) fun _ ↦
      allQueriesSatisfy_bind (walkS_topNode _ _ _ _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _)
    fun _ ↦ walkS_tweakableHash _ _ _ (walkS_rootsPayload _)

theorem walkS_coordOpen (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (mark : CoordMark) (seed : Sphincs.MasterSeed) :
    AllQueriesSatisfy (Seeded.coordOpen p index c mark seed :
      OracleComp Sphincs.HashSpec CoordOpening) (WalkSQ p) := by
  unfold Seeded.coordOpen
  exact allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦
    allQueriesSatisfy_bind (walkS_forestSecrets _ _ _ _ _ _ _) fun _ ↦
      allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦ walkS_forestWalk _ _ _ _ _ _ _ _ _ _)
        fun _ ↦ allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦ walkS_subNode _ _ _ _ _ _ _ _)
          fun _ ↦ allQueriesSatisfy_pure _ _) fun _ ↦
    allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦ walkS_topNode _ _ _ _ _ _) fun _ ↦
      allQueriesSatisfy_pure _ _

theorem walkS_forestOpen (p : Sphincs.PublicParameter) (index : Index) (marks : Coord → CoordMark)
    (seed : Sphincs.MasterSeed) :
    AllQueriesSatisfy (Seeded.forestOpen p index marks seed :
      OracleComp Sphincs.HashSpec (Coord → CoordOpening)) (WalkSQ p) :=
  walkS_sequenceFin _ fun _ ↦ walkS_coordOpen _ _ _ _ _

/-! ### Verification -/

theorem walkS_treeFold (p : Sphincs.PublicParameter) (lay : Sphincs.Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : ℕ → Sphincs.Digest) : ∀ (levels : ℕ) (v : Sphincs.Digest),
      AllQueriesSatisfy (treeFold p lay tree leaf path levels v :
        OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p)
  | 0, _ => allQueriesSatisfy_pure _ _
  | levels + 1, v => by
    simp only [treeFold]
    refine allQueriesSatisfy_bind (walkS_treeFold p lay tree leaf path levels v) fun _ ↦ ?_
    split <;> exact walkS_tweakableHash _ _ _ (walkS_nodePayload _ _)

theorem walkS_subFold (p : Sphincs.PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (path : Fin subHeight → Sphincs.Digest) :
    ∀ (levels : ℕ) (v : Sphincs.Digest), AllQueriesSatisfy (subFold p index c s j a path levels v :
      OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p)
  | 0, _ => allQueriesSatisfy_pure _ _
  | levels + 1, v => by
    simp only [subFold]
    refine allQueriesSatisfy_bind (walkS_subFold p index c s j a path levels v) fun _ ↦ ?_
    split
    · split <;> exact walkS_tweakableHash _ _ _ (walkS_nodePayload _ _)
    · exact allQueriesSatisfy_pure _ _

theorem walkS_topFold (p : Sphincs.PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (path : Fin topHeight → Sphincs.Digest) :
    ∀ (levels : ℕ) (v : Sphincs.Digest), AllQueriesSatisfy (topFold p index c s path levels v :
      OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p)
  | 0, _ => allQueriesSatisfy_pure _ _
  | levels + 1, v => by
    simp only [topFold]
    refine allQueriesSatisfy_bind (walkS_topFold p index c s path levels v) fun _ ↦ ?_
    split
    · split <;> exact walkS_tweakableHash _ _ _ (walkS_nodePayload _ _)
    · exact allQueriesSatisfy_pure _ _

theorem walkS_coordRecover (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (mark : CoordMark) (opening : CoordOpening) :
    AllQueriesSatisfy (coordRecover p index c mark opening :
      OracleComp Sphincs.HashSpec (Sphincs.Digest × Sphincs.Digest)) (WalkSQ p) := by
  unfold coordRecover childRecover childLeafHash superHash
  refine allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦
    allQueriesSatisfy_bind (allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦
      walkS_forestWalk _ _ _ _ _ _ _ _ _ _) fun e ↦
        walkS_tweakableHash _ _ _ (walkS_flatMap_length (n := 5) e _ walkS_bytes16)) fun _ ↦
      allQueriesSatisfy_bind (walkS_subFold _ _ _ _ _ _ _ _ _) fun _ ↦
        allQueriesSatisfy_pure _ _) fun _ ↦
    allQueriesSatisfy_bind (walkS_tweakableHash _ _ _ ?_) fun _ ↦
      allQueriesSatisfy_bind (walkS_topFold _ _ _ _ _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _
  simp only [superPayload, List.length_append]
  have := walkS_nodePayload
  grind

theorem walkS_otsLeaf (p : Sphincs.PublicParameter) (lay : Sphincs.Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (msg : Sphincs.Digest) (counter : Counter)
    (values : Sphincs.ChainIndex → Sphincs.Digest) :
    AllQueriesSatisfy (otsLeaf p lay tree leaf msg counter values :
      OracleComp Sphincs.HashSpec (Option Sphincs.Digest)) (WalkSQ p) := by
  unfold otsLeaf recoverChain
  refine allQueriesSatisfy_bind (walkS_encode _ _ _ _ _ _) fun o ↦ ?_
  rcases o with _ | e
  · exact allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦ walkS_chainWalk _ _ _ _ _ _ _ _)
      fun _ ↦ allQueriesSatisfy_bind (walkS_leafHash _ _ _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _

theorem walkS_verifyLayers (p : Sphincs.PublicParameter) (index : Index) (σ : Sphincs.Signature)
    (remaining : ℕ) (msg : Sphincs.Digest) :
    AllQueriesSatisfy (verifyLayers p index σ remaining msg :
      OracleComp Sphincs.HashSpec (Option Sphincs.Digest)) (WalkSQ p) := by
  induction remaining generalizing msg with
  | zero => exact allQueriesSatisfy_pure _ _
  | succ remaining ih =>
    simp only [verifyLayers]
    split
    next hl =>
      generalize layerHeight ⟨remaining, hl⟩ = L
      refine allQueriesSatisfy_bind (walkS_otsLeaf _ _ _ _ _ _ _) fun o ↦ ?_
      rcases o with _ | v
      · exact allQueriesSatisfy_pure _ _
      · exact allQueriesSatisfy_bind (walkS_treeFold _ _ _ _ _ _ _) fun _ ↦ ih _
    next => exact allQueriesSatisfy_pure _ _

/-- **Every query of leanSPHINCS's verification is a scheme input of the key's parameter, not
shaped as a derivation.** -/
theorem sphincs_verify_queriesN (pk : Sphincs.PublicKey) (m : Sphincs.Message)
    (σ : Sphincs.Signature) :
    QueriesSat (Concrete.verify pk m σ : OracleComp Sphincs.HashSpec Bool)
      (SchemeInputN (bytesLE 16 pk.parameter)) := by
  rw [queriesSat_iff]
  simp only [Concrete.verify, messageDigest, messageDigestCall, bind_assoc, pure_bind]
  refine allQueriesSatisfy_bind (walkS_oracleHash _ ?_) fun _ ↦
    allQueriesSatisfy_bind (?_ : AllQueriesSatisfy (forestRecover _ _ _ _) _) fun _ ↦
      allQueriesSatisfy_bind (walkS_verifyLayers _ _ _ _ _) fun o ↦ ?_
  · exact sphincs_schemeInputN _ _ _ (sphincs_hashDomain_tag _)
      (by simp [messageDigestPayload, bytesLE])
  · unfold forestRecover
    exact allQueriesSatisfy_bind (walkS_sequenceFin _ fun _ ↦ walkS_coordRecover _ _ _ _ _)
      fun _ ↦ walkS_tweakableHash _ _ _ (walkS_rootsPayload _)
  · rcases o with _ | r <;> exact allQueriesSatisfy_pure _ _

/-- **Every query of leanSPHINCS's verification is a scheme input of the key's parameter.** -/
theorem sphincs_verify_queries (pk : Sphincs.PublicKey) (m : Sphincs.Message)
    (σ : Sphincs.Signature) :
    QueriesSat (Concrete.verify pk m σ : OracleComp Sphincs.HashSpec Bool)
      (SchemeInput (bytesLE 16 pk.parameter)) :=
  (queriesSat_iff _ _).mpr (((queriesSat_iff _ _).mp (sphincs_verify_queriesN pk m σ)).mono
    fun _ (h : SchemeInputN _ _) ↦ h.1)

/-! ### The parameter set's parts: signer and key generation -/

variable [Sphincs.Params]

omit [Sphincs.Params] in
theorem walkS_surrogate (p : Sphincs.PublicParameter) (seed : Sphincs.MasterSeed) (level : ℕ) :
    AllQueriesSatisfy (Seeded.surrogate p seed level :
      OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p) := by
  unfold Seeded.surrogate deriveKey
  split
  · exact allQueriesSatisfy_bind (walkS_derive _ _ (by simp) _) fun _ ↦ allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_pure _ _

theorem walkS_treePath (p : Sphincs.PublicParameter) (lay : Sphincs.Layer) (tree : TreeIndex)
    (seed : Sphincs.MasterSeed) (leaf : LeafIndex) :
    AllQueriesSatisfy (Seeded.treePath p lay tree seed leaf : OracleComp Sphincs.HashSpec _)
      (WalkSQ p) := by
  unfold Seeded.treePath
  refine walkS_sequenceFin _ fun level ↦ ?_
  split
  · exact walkS_treeNode _ _ _ _ _ _
  · exact walkS_surrogate _ _ _

theorem walkS_spineNode (p : Sphincs.PublicParameter) (lay : Sphincs.Layer) (tree : TreeIndex)
    (seed : Sphincs.MasterSeed) : ∀ steps : ℕ,
      AllQueriesSatisfy (Seeded.spineNode p lay tree seed steps :
        OracleComp Sphincs.HashSpec Sphincs.Digest) (WalkSQ p)
  | 0 => walkS_treeNode _ _ _ _ _ _
  | steps + 1 => by
    simp only [Seeded.spineNode]
    refine allQueriesSatisfy_bind (walkS_spineNode p lay tree seed steps) fun _ ↦
      allQueriesSatisfy_bind (walkS_surrogate _ _ _) fun _ ↦ ?_
    split <;> exact walkS_tweakableHash _ _ _ (walkS_nodePayload _ _)

theorem walkS_signDigestLoop (sk : Seeded.SecretKey) (msg : Sphincs.Message) :
    ∀ (attempts : ℕ) (r : Sphincs.Randomness), AllQueriesSatisfy
      (Seeded.signDigestLoop sk msg attempts r : OracleComp Sphincs.HashSpec _)
      (WalkSQ sk.parameter)
  | 0, _ => allQueriesSatisfy_pure _ _
  | attempts + 1, r => by
    simp only [Seeded.signDigestLoop, Seeded.signAttempt, messageDigestCall, bind_assoc]
    refine allQueriesSatisfy_bind (walkS_oracleHash _ ?_) fun _ ↦ ?_
    · exact sphincs_schemeInputN _ _ _ (sphincs_hashDomain_tag _)
        (by simp [messageDigestPayload, bytesLE])
    · split
      · rw [pure_bind]
        exact allQueriesSatisfy_pure _ _
      · rw [pure_bind]
        exact walkS_signDigestLoop sk msg attempts _

theorem walkS_signLayer (sk : Seeded.SecretKey) (index : Index) (lay : Sphincs.Layer) :
    AllQueriesSatisfy (Seeded.signLayer sk index lay : OracleComp Sphincs.HashSpec _)
      (WalkSQ sk.parameter) := by
  unfold Seeded.signLayer Seeded.layerMessage Seeded.otsSign
  refine allQueriesSatisfy_bind (walkS_forestKey _ _ _) fun _ ↦
    allQueriesSatisfy_bind (walkS_otsSignFrom _ _ _ _ _ _ _ _) fun o ↦ ?_
  rcases o with _ | ⟨counter, values⟩
  · exact allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_bind (walkS_treePath _ _ _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _

/-- **Every query of leanSPHINCS's signer is a scheme input of the key's parameter, not shaped as
a derivation.** -/
theorem sphincs_sign_queriesN (sk : Seeded.SecretKey) (m : Sphincs.Message) :
    QueriesSat (Seeded.sign sk m : OracleComp Sphincs.HashSpec _)
      (SchemeInputN (bytesLE 16 sk.parameter)) := by
  rw [queriesSat_iff]
  have hD := walkS_signDigestLoop sk m
  have hF := walkS_forestOpen sk.parameter
  have hL := walkS_signLayer sk
  simp only [Seeded.sign, deriveRandomizer, messageDigest, messageDigestCall, sequenceLayers,
    bind_assoc, pure_bind]
  generalize digestAttemptLimit = A
  generalize (Seeded.signDigestLoop sk m : ℕ → Sphincs.Randomness → OracleComp Sphincs.HashSpec _)
    = DL at hD ⊢
  generalize (Seeded.forestOpen sk.parameter : Index → (Coord → CoordMark) → Sphincs.MasterSeed →
    OracleComp Sphincs.HashSpec _) = FO at hF ⊢
  generalize (Seeded.signLayer sk : Index → (lay : Sphincs.Layer) →
    OracleComp Sphincs.HashSpec (Option (LayerSignature lay))) = SL at hL ⊢
  refine allQueriesSatisfy_bind (walkS_oracleHash _ ?_) fun _ ↦
    allQueriesSatisfy_bind (hD _ _) fun o ↦ ?_
  · unfold randomizerHashInput
    rw [List.append_assoc _ (bytesLE 32 sk.seed)]
    exact sphincs_schemeInputN _ _ _ (by decide) (by simp [bytesLE])
  · rcases o with _ | ⟨r, i⟩
    · exact allQueriesSatisfy_pure _ _
    · refine allQueriesSatisfy_bind (walkS_oracleHash _ ?_) fun _ ↦
        allQueriesSatisfy_bind (hF _ _ _) fun _ ↦ allQueriesSatisfy_bind (hL _ _) fun o' ↦ ?_
      · exact sphincs_schemeInputN _ _ _ (sphincs_hashDomain_tag _)
          (by simp [messageDigestPayload, bytesLE])
      · rcases o' with _ | top <;> exact allQueriesSatisfy_pure _ _

/-- **Every query of leanSPHINCS's signer is a scheme input of the key's parameter.** -/
theorem sphincs_sign_queries (sk : Seeded.SecretKey) (m : Sphincs.Message) :
    QueriesSat (Seeded.sign sk m : OracleComp Sphincs.HashSpec _)
      (SchemeInput (bytesLE 16 sk.parameter)) :=
  (queriesSat_iff _ _).mpr (((queriesSat_iff _ _).mp (sphincs_sign_queriesN sk m)).mono
    fun _ (h : SchemeInputN _ _) ↦ h.1)

/-! ### Key generation -/

omit [Sphincs.Params] in
/-- The seed hash `"leanSPHINCS" ‖ S0` is a derivation. -/
theorem sphincs_schemeSeedInput_derivShape (s : Sphincs.MasterSeed) :
    DerivShape (schemeSeedInput s) :=
  Or.inr (Or.inl ⟨by simp [schemeSeedInput, Sphincs.seedTag, bytesLE], List.prefix_append _ _⟩)

omit [Sphincs.Params] in
/-- The parameter derivation `0^16 ‖ A_param ‖ S` is a derivation. -/
theorem sphincs_paramInput_derivShape (s : Sphincs.MasterSeed) :
    DerivShape (keygenHashInput 0 .parameter s) := by
  refine Or.inr (Or.inr ⟨by simp [keygenHashInput, fieldBytes, bytesLE], ?_⟩)
  have h : bytesLE 16 (0 : Sphincs.PublicParameter) ++ fieldBytes (keygenDomainFields .parameter) =
      paramPrefix := by decide
  rw [keygenHashInput, h]
  exact List.prefix_append _ _

/-- Key generation, its two derivations made explicit: the spine under the derived parameter. -/
theorem sphincs_keygenFromSeed_eq (seed : Sphincs.MasterSeed) :
    Seeded.keygenFromSeed seed =
      (liftM (Sphincs.HashSpec.query (schemeSeedInput seed)) : OracleComp Sphincs.HashSpec _) >>=
        fun s ↦ (liftM (Sphincs.HashSpec.query (keygenHashInput 0 .parameter s)) :
          OracleComp Sphincs.HashSpec _) >>= fun o ↦
          (Seeded.spineNode (truncateHash o) topLayer rootTree s (totalHeight - subtreeHeight) :
            OracleComp Sphincs.HashSpec Sphincs.Digest) >>= fun root ↦
            pure (⟨root, truncateHash o⟩, ⟨s, truncateHash o, root⟩) := by
  simp only [Seeded.keygenFromSeed, Seeded.keygenFromMaster, Seeded.treeRoot, schemeSeed,
    deriveKey, oracleHash, bind_assoc, pure_bind]
  rfl

/-- **Key generation's queries**: on every logged run, each query is a derivation or a scheme input
of the output's parameter, not shaped as a derivation. -/
theorem sphincs_keygen_queriesN (seed : Sphincs.MasterSeed) :
    ∀ z ∈ support ((simulateQ
        (QueryImpl.ofLift Sphincs.HashSpec (OracleComp Sphincs.HashSpec)).withLogging
        (Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1), DerivShape x ∨ SchemeInputN (bytesLE 16 z.1.2.parameter) x := by
  show ∀ z ∈ support ((simulateQ loggingOracle (Seeded.keygenFromSeed seed)).run), _
  intro z hz x hx
  rw [sphincs_keygenFromSeed_eq] at hz
  generalize totalHeight - subtreeHeight = K at hz
  rw [run_simulateQ_loggingOracle_query_bind, support_bind] at hz
  simp only [Set.mem_iUnion, support_map] at hz
  obtain ⟨s, -, z1, hz1, rfl⟩ := hz
  rw [run_simulateQ_loggingOracle_query_bind, support_bind] at hz1
  simp only [Set.mem_iUnion, support_map] at hz1
  obtain ⟨o, -, z2, hz2, rfl⟩ := hz1
  have hall : AllQueriesSatisfy ((Seeded.spineNode (truncateHash o) topLayer rootTree s K :
      OracleComp Sphincs.HashSpec Sphincs.Digest) >>= fun root ↦
        (pure (⟨root, truncateHash o⟩, ⟨s, truncateHash o, root⟩) :
          OracleComp Sphincs.HashSpec (Sphincs.PublicKey × Seeded.SecretKey)))
        (WalkSQ (truncateHash o)) :=
    allQueriesSatisfy_bind (walkS_spineNode _ _ _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _
  have hpar : z2.1.2.parameter = truncateHash o := by
    have h1 : z2.1 ∈ Prod.fst '' support _ := ⟨z2, hz2, rfl⟩
    rw [← support_map, loggingOracle.support_fst_map_run_simulateQ, mem_support_bind_iff] at h1
    obtain ⟨root, -, h⟩ := h1
    rw [mem_support_pure_iff] at h
    rw [h]
  simp only [List.map_cons, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | rfl | ⟨e, he, rfl⟩
  · exact Or.inl (sphincs_schemeSeedInput_derivShape seed)
  · exact Or.inl (sphincs_paramInput_derivShape s)
  · right
    dsimp only
    rw [hpar]
    exact holds_of_mem_log_of_mem_support_run_simulateQ hall hz2 e he

/-- **Key generation's queries** (the interface of P2d and P7): each query is a derivation or a
scheme input of the output's parameter. -/
theorem sphincs_keygen_queries (seed : Sphincs.MasterSeed) :
    ∀ z ∈ support ((simulateQ
        (QueryImpl.ofLift Sphincs.HashSpec (OracleComp Sphincs.HashSpec)).withLogging
        (Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1), DerivShape x ∨ SchemeInput (bytesLE 16 z.1.2.parameter) x :=
  fun z hz x hx ↦ (sphincs_keygen_queriesN seed z hz x hx).imp_right (·.1)

/-- **The keys carry the same parameter.** -/
theorem sphincs_keygen_param (seed : Sphincs.MasterSeed) :
    ∀ z ∈ support (Seeded.keygenFromSeed seed), z.1.parameter = z.2.parameter := by
  intro z hz
  rw [sphincs_keygenFromSeed_eq] at hz
  generalize totalHeight - subtreeHeight = K at hz
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨_, -, _, -, _, -, rfl⟩ := hz
  rfl

/-- **Key generation makes at most two queries shaped as derivations.** -/
theorem sphincs_keygen_deriv_count (seed : Sphincs.MasterSeed) :
    IsQueryBoundP (Seeded.keygenFromSeed seed) DerivShapeQ 2 := by
  rw [sphincs_keygenFromSeed_eq]
  generalize totalHeight - subtreeHeight = K
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by norm_num), fun s ↦ ?_⟩
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by split <;> norm_num), fun o ↦ ?_⟩
  refine walk_isQueryBoundP_of_all ?_ _
  exact (allQueriesSatisfy_bind (walkS_spineNode _ _ _ _ _) fun _ ↦
    allQueriesSatisfy_pure _ _).mono fun _ (h : SchemeInputN _ _) ↦ h.2

end
end LeanVM.E2E
