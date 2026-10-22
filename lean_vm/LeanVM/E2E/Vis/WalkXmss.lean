/-
  LeanVM.E2E.Vis.WalkXmss

  W-vis, P2b: every hash query of leanXMSS's key generation, signer and verifier is a scheme input
  of the key's parameter (`P ‖ A ‖ payload`, at least 48 bytes) or one of key generation's two
  derivations.
-/

module

public import LeanVM.E2E.Vis.Shape

/-!
# leanXMSS's queries (W-vis, P2b)

Every leanXMSS hash input is `P ‖ A ‖ payload` (`LeanXmss.tweakableHashInput`,
`keygenHashInput`, `randomizerHashInput`): the 16 bytes of the parameter `P`, a 16-byte address
`A` whose last 8 bytes are zero (`AddrOK`), and a payload of at least 16 bytes. The exceptions are
key generation's two derivations, `"leanXMSS" ‖ S0` and `0^16 ‖ A_param ‖ S` (`DerivShape`).

* `SchemeInput p x`: `x` is `p ‖ A ‖ …` with `A` an address, and at least 48 bytes.
* `SchemeInputN p x`: the same, and not shaped as a derivation (`¬ DerivShape x`): every
  address the walks use has a type byte other than `A_param`'s `5`.
* `xmss_sign_queries`, `xmss_verify_queries`: every query of `Seeded.sign` (resp.
  `Concrete.verify`) is a `SchemeInputN` of the key's parameter (`*_queriesN`), hence a
  `SchemeInput`.
* `xmss_keygen_queries`: on every logged run of `Seeded.keygenFromSeed`, every query is a
  derivation or a `SchemeInputN` of the parameter the run outputs; `xmss_keygen_param`: the
  public and secret keys carry the same parameter; `xmss_keygen_deriv_count`: at most two
  queries are shaped as derivations.

The walks follow `Reduction/XmssBound.lean`, with `AllQueriesSatisfy` in place of the counts.
-/

namespace LeanVM.E2E

open OracleSpec OracleComp

@[expose] public section

/-! ## Interfaces -/

/-- **Every query of `oa` satisfies `P`.** -/
abbrev QueriesSat {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (oa : OracleComp spec α)
    (P : ι → Prop) [DecidablePred P] : Prop := IsQueryBoundP oa (fun t ↦ ¬ P t) 0

/-- `QueriesSat` is VCVio's `AllQueriesSatisfy`. -/
theorem queriesSat_iff {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (oa : OracleComp spec α) (P : ι → Prop) [DecidablePred P] :
    QueriesSat oa P ↔ AllQueriesSatisfy oa P :=
  isQueryBoundP_zero_iff oa P

/-- No `p`-query at all: a `p`-bound at any budget. -/
theorem walk_isQueryBoundP_of_all {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {p : ι → Prop} [DecidablePred p] {oa : OracleComp spec α}
    (h : AllQueriesSatisfy oa (fun t ↦ ¬ p t)) (n : ℕ) : IsQueryBoundP oa p n :=
  ((isQueryBoundP_congr_pred (fun t ↦ not_not (a := p t))).mp
    ((isQueryBoundP_zero_iff oa _).mpr h)).mono (Nat.zero_le n)

/-- **Prefixed by the parameter `p` and an address.** -/
def ParamPrefixed (p : List UInt8) (x : List UInt8) : Prop := ∃ a, AddrOK a ∧ p ++ a <+: x

theorem paramPrefixed_iff (p x : List UInt8) :
    ParamPrefixed p x ↔ p <+: x ∧ AddrOK ((x.drop p.length).take 16) := by
  constructor
  · rintro ⟨a, ha, r, rfl⟩
    refine ⟨⟨a ++ r, by rw [List.append_assoc]⟩, ?_⟩
    rw [List.append_assoc, List.drop_left, List.take_left' ha.1]
    exact ha
  · rintro ⟨⟨r, rfl⟩, ha⟩
    refine ⟨_, ha, ?_⟩
    rw [List.drop_left]
    exact (List.prefix_append_right_inj p).mpr (List.take_prefix _ _)

instance (p x : List UInt8) : Decidable (ParamPrefixed p x) :=
  decidable_of_iff _ (paramPrefixed_iff p x).symm

/-- **A scheme input of the parameter `p`**: `p ‖ A ‖ …`, at least 48 bytes. -/
def SchemeInput (p : List UInt8) (x : List UInt8) : Prop := ParamPrefixed p x ∧ 48 ≤ x.length

instance (p x : List UInt8) : Decidable (SchemeInput p x) := inferInstanceAs (Decidable (_ ∧ _))

/-- **A scheme input not shaped as a derivation.** -/
def SchemeInputN (p : List UInt8) (x : List UInt8) : Prop := SchemeInput p x ∧ ¬ DerivShape x

instance (p x : List UInt8) : Decidable (SchemeInputN p x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The derivation shapes, as a predicate on the schemes' hash inputs. -/
abbrev DerivShapeQ (x : List UInt8) : Prop := DerivShape x

/-! ## Static facts -/

/-- `paramPrefix` is 32 bytes. -/
theorem paramPrefix_length : paramPrefix.length = 32 := by decide

/-- The type byte of `A_param`. -/
theorem paramPrefix_byte23 : (paramPrefix.drop 16)[7]? = some 5 := by decide

/-- A 16-byte prefix, an address other than `A_param` and a payload of at least 16 bytes: a scheme
input not shaped as a derivation. -/
theorem schemeInputN_append {p a r : List UInt8} (hp : p.length = 16) (ha : AddrOK a)
    (hne : a ≠ paramPrefix.drop 16) (hr : 16 ≤ r.length) : SchemeInputN p (p ++ a ++ r) := by
  have hl : (p ++ a ++ r).length = 32 + r.length := by
    simp only [List.length_append, hp, ha.1]
  refine ⟨⟨⟨a, ha, List.prefix_append _ _⟩, by omega⟩, ?_⟩
  rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, t, ht⟩)
  · omega
  · omega
  · have h32 := (List.append_inj ht (by simp [paramPrefix_length, hp, ha.1])).1
    apply hne
    rw [h32, List.drop_left' hp]

/-- An address byte list whose type byte is not `A_param`'s. -/
theorem ne_paramAddr_of_byte7 {b : List UInt8} {s : BitVec 3} {t : BitVec 5} (ht : t ≠ 5#5)
    (hb : b[7]? = some (UInt8.ofBitVec ((s ++ t).extractLsb' 0 8))) : b ≠ paramPrefix.drop 16 := by
  rintro rfl
  rw [paramPrefix_byte23, Option.some_inj] at hb
  have hv : (s ++ t) = 5#8 := by
    have := congrArg UInt8.toBitVec hb
    rw [UInt8.toBitVec_ofBitVec, BitVec.extractLsb'_eq_self] at this
    exact this.symm
  have := congrArg (BitVec.extractLsb' 0 5) hv
  rw [BitVec.extractLsb'_append_eq_right] at this
  exact ht (this.trans (by decide))

section Xmss

open LeanXmss LeanXmss.Concrete

/-- A leanXMSS address is an address. -/
theorem xmss_addrOK (f : TweakFields) : AddrOK (fieldBytes f) := by
  refine ⟨by simp [fieldBytes, bytesLE], ?_⟩
  have h : (fieldBytes f).drop 8 = bytesLE 8 0 := by
    rw [show fieldBytes f = (bytesLE 4 f.lo ++ bytesLE 3 f.hi ++ bytesLE 1 (f.step ++ f.tag)) ++
      bytesLE 8 0 from rfl, List.drop_left' (by simp [bytesLE])]
  rw [h]
  decide

/-- A leanXMSS address of another type than `A_param`'s. -/
theorem xmss_fieldBytes_ne (f : TweakFields) (h : f.tag ≠ 5#5) :
    fieldBytes f ≠ paramPrefix.drop 16 :=
  ne_paramAddr_of_byte7 h (s := f.step) rfl

/-- A leanXMSS input `P ‖ A ‖ payload`, `A` of another type than `A_param`'s. -/
theorem xmss_schemeInputN (p : PublicParameter) (f : TweakFields) (r : HashInput)
    (hf : f.tag ≠ 5#5) (hr : 16 ≤ r.length) :
    SchemeInputN (bytesLE 16 p) (bytesLE 16 p ++ fieldBytes f ++ r) :=
  schemeInputN_append (by simp [bytesLE]) (xmss_addrOK f) (xmss_fieldBytes_ne f hf) hr

/-- No verification address has `A_param`'s type. -/
theorem xmss_hashDomain_tag (d : HashDomain) : (hashDomainFields d).tag ≠ 5#5 := by
  cases d <;> (simp only [hashDomainFields, tweakFields]; decide)

/-- The walks' predicate. -/
abbrev WalkXQ (p : PublicParameter) : HashInput → Prop := SchemeInputN (bytesLE 16 p)

/-- One oracle call. -/
theorem walkX_oracleHash {P : HashInput → Prop} (x : HashInput) (hx : P x) :
    AllQueriesSatisfy (oracleHash x : OracleComp LeanXmss.HashSpec HashOutput) P := by
  change AllQueriesSatisfy ((liftM (LeanXmss.HashSpec.query x) : OracleComp LeanXmss.HashSpec _) >>=
    fun o ↦ pure o) P
  exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hx, fun _ ↦ allQueriesSatisfy_pure _ _⟩

/-- A tweakable hash with a payload of at least 16 bytes. -/
theorem walkX_tweakableHash (p : PublicParameter) (d : HashDomain) (x : HashInput)
    (hx : 16 ≤ x.length) :
    AllQueriesSatisfy (tweakableHash p d x : OracleComp LeanXmss.HashSpec Digest) (WalkXQ p) :=
  allQueriesSatisfy_bind (walkX_oracleHash _ (xmss_schemeInputN p _ x (xmss_hashDomain_tag d) hx))
    fun _ ↦ allQueriesSatisfy_pure _ _

/-- A sequence of computations, each asking only `P`-queries. -/
theorem walkX_sequenceFin {α : Type} {P : HashInput → Prop} :
    ∀ {n : ℕ} (c : Fin n → OracleComp LeanXmss.HashSpec α), (∀ i, AllQueriesSatisfy (c i) P) →
      AllQueriesSatisfy (sequenceFin c) P
  | 0, _, _ => allQueriesSatisfy_pure _ _
  | n + 1, c, h => by
    simp only [sequenceFin]
    exact allQueriesSatisfy_bind (h 0) fun _ ↦
      allQueriesSatisfy_bind (walkX_sequenceFin (fun i ↦ c i.succ) fun i ↦ h i.succ)
        fun _ ↦ allQueriesSatisfy_pure _ _

/-- `bytesLE 16` over `n + 1` digests: at least 16 bytes. -/
theorem walkX_flatMap_length {n : ℕ} (v : Fin (n + 1) → BitVec (8 * 16)) :
    16 ≤ ((List.ofFn v).flatMap (bytesLE 16)).length := by
  rw [List.ofFn_succ, List.flatMap_cons, List.length_append]
  simp only [bytesLE, List.length_ofFn]
  omega

theorem walkX_chainWalk (p : PublicParameter) (lay : Layer) (key : KeyIndex) (c : ChainIndex)
    (start : ℕ) : ∀ (steps : ℕ) (v : Digest),
      AllQueriesSatisfy (chainWalk p lay key c start steps v : OracleComp LeanXmss.HashSpec Digest)
        (WalkXQ p)
  | 0, _ => allQueriesSatisfy_pure _ _
  | steps + 1, v => by
    simp only [chainWalk]
    refine allQueriesSatisfy_bind (walkX_chainWalk p lay key c start steps v) fun _ ↦ ?_
    split
    · exact walkX_tweakableHash _ _ _ (by simp [chainPayload, bytesLE])
    · exact allQueriesSatisfy_pure _ _

theorem walkX_otsSecrets (p : PublicParameter) (lay : Layer) (key : KeyIndex) (seed : MasterSeed) :
    AllQueriesSatisfy (Seeded.otsSecrets p lay key seed :
      OracleComp LeanXmss.HashSpec (ChainIndex → Digest)) (WalkXQ p) := by
  unfold Seeded.otsSecrets
  refine allQueriesSatisfy_bind (walkX_sequenceFin _ fun pair ↦ walkX_oracleHash _ ?_)
    fun _ ↦ allQueriesSatisfy_pure _ _
  exact xmss_schemeInputN p _ _ (by simp only [keygenDomainFields, tweakFields]; decide)
    (by simp [bytesLE])

theorem walkX_chainWalks (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (steps : ChainIndex → ℕ) (secrets : ChainIndex → Digest) :
    AllQueriesSatisfy (sequenceFin fun chainIdx ↦ chainWalk p lay key chainIdx 0 (steps chainIdx)
      (secrets chainIdx) : OracleComp LeanXmss.HashSpec (ChainIndex → Digest)) (WalkXQ p) :=
  walkX_sequenceFin _ fun _ ↦ walkX_chainWalk _ _ _ _ _ _ _

theorem walkX_leafHash (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (e : ChainIndex → Digest) :
    AllQueriesSatisfy (leafHash p lay key e : OracleComp LeanXmss.HashSpec Digest) (WalkXQ p) :=
  walkX_tweakableHash _ _ _ (walkX_flatMap_length (n := 57) e)

theorem walkX_nodePayload (l r : Digest) : 16 ≤ (nodePayload l r).length := by
  simp [nodePayload, bytesLE]

theorem walkX_treeNode (p : PublicParameter) (lay : Layer) (seed : MasterSeed) :
    ∀ (level node : ℕ), AllQueriesSatisfy (Seeded.treeNode p lay seed level node :
      OracleComp LeanXmss.HashSpec Digest) (WalkXQ p)
  | 0, node => by
    simp only [Seeded.treeNode, Seeded.oneTimePublicKey, bind_assoc]
    exact allQueriesSatisfy_bind (walkX_otsSecrets _ _ _ _) fun _ ↦
      allQueriesSatisfy_bind (walkX_chainWalks _ _ _ _ _) fun _ ↦ walkX_leafHash _ _ _ _
  | level + 1, node => by
    simp only [Seeded.treeNode]
    exact allQueriesSatisfy_bind (walkX_treeNode p lay seed level _) fun _ ↦
      allQueriesSatisfy_bind (walkX_treeNode p lay seed level _) fun _ ↦
        walkX_tweakableHash _ _ _ (walkX_nodePayload _ _)

theorem walkX_otsSignFrom (p : PublicParameter) (lay : Layer) (key : KeyIndex) (seed : MasterSeed)
    (msg : HashInput) (base : Randomness) : ∀ (attempts trial : ℕ),
      AllQueriesSatisfy (Seeded.otsSignFrom p lay key seed msg base attempts trial :
        OracleComp LeanXmss.HashSpec _) (WalkXQ p)
  | 0, _ => allQueriesSatisfy_pure _ _
  | attempts + 1, trial => by
    simp only [Seeded.otsSignFrom]
    refine allQueriesSatisfy_bind (walkX_tweakableHash _ _ _ (by simp [bytesLE])) fun d ↦ ?_
    split
    · exact allQueriesSatisfy_bind (walkX_otsSecrets _ _ _ _) fun _ ↦
        allQueriesSatisfy_bind (walkX_chainWalks _ _ _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _
    · exact walkX_otsSignFrom p lay key seed msg base attempts (trial + 1)

theorem walkX_treePath (p : PublicParameter) (lay : Layer) (seed : MasterSeed) (key : KeyIndex) :
    AllQueriesSatisfy (Seeded.treePath p lay seed key : OracleComp LeanXmss.HashSpec _)
      (WalkXQ p) :=
  walkX_sequenceFin _ fun _ ↦ walkX_treeNode _ _ _ _ _

theorem walkX_signLayer (sk : Seeded.SecretKey) (lay : Layer) (key : KeyIndex) (msg : HashInput) :
    AllQueriesSatisfy (Seeded.signLayer sk lay key msg : OracleComp LeanXmss.HashSpec _)
      (WalkXQ sk.parameter) := by
  simp only [Seeded.signLayer, Seeded.otsSign, deriveRandomizer, bind_assoc, pure_bind]
  refine allQueriesSatisfy_bind (walkX_oracleHash _ ?_) fun _ ↦
    allQueriesSatisfy_bind (walkX_otsSignFrom _ _ _ _ _ _ _ _) fun o ↦ ?_
  · unfold randomizerHashInput
    rw [List.append_assoc _ (bytesLE 32 sk.seed)]
    exact xmss_schemeInputN _ _ _ (by simp only [tweakFields]; decide) (by simp [bytesLE])
  · rcases o with _ | ⟨r, v⟩
    · exact allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_bind (walkX_treePath _ _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _

/-- **Every query of leanXMSS's signer is a scheme input of the key's parameter, not shaped as a
derivation.** -/
theorem xmss_sign_queriesN (sk : Seeded.SecretKey) (i : LeafIndex) (m : Message) :
    QueriesSat (Seeded.sign sk i m : OracleComp LeanXmss.HashSpec _)
      (SchemeInputN (bytesLE 16 sk.parameter)) := by
  rw [queriesSat_iff]
  simp only [Seeded.sign]
  generalize layerHeight = L
  refine allQueriesSatisfy_bind (walkX_signLayer _ _ _ _) fun o ↦ ?_
  rcases o with _ | bottom
  · exact allQueriesSatisfy_pure _ _
  · refine allQueriesSatisfy_bind (walkX_treeNode _ _ _ _ _) fun _ ↦
      allQueriesSatisfy_bind (walkX_signLayer _ _ _ _) fun o' ↦ ?_
    rcases o' with _ | top <;> exact allQueriesSatisfy_pure _ _

/-- **Every query of leanXMSS's signer is a scheme input of the key's parameter.** -/
theorem xmss_sign_queries (sk : Seeded.SecretKey) (i : LeafIndex) (m : Message) :
    QueriesSat (Seeded.sign sk i m : OracleComp LeanXmss.HashSpec _)
      (SchemeInput (bytesLE 16 sk.parameter)) :=
  (queriesSat_iff _ _).mpr (((queriesSat_iff _ _).mp (xmss_sign_queriesN sk i m)).mono
    fun _ (h : SchemeInputN _ _) ↦ h.1)

/-! ### Verification -/

theorem walkX_otsLeaf (p : PublicParameter) (lay : Layer) (key : KeyIndex) (msg : HashInput)
    (r : Randomness) (values : ChainIndex → Digest) :
    AllQueriesSatisfy (otsLeaf p lay key msg r values : OracleComp LeanXmss.HashSpec _)
      (WalkXQ p) := by
  unfold otsLeaf
  refine allQueriesSatisfy_bind (walkX_tweakableHash _ _ _ (by simp [bytesLE]))
    fun d ↦ ?_
  split
  · exact allQueriesSatisfy_bind (walkX_sequenceFin _ fun _ ↦ walkX_chainWalk _ _ _ _ _ _ _)
      fun _ ↦ allQueriesSatisfy_bind (walkX_leafHash _ _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_pure _ _

theorem walkX_treeFold (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) : ∀ (levels : ℕ) (v : Digest),
      AllQueriesSatisfy (treeFold p lay key path levels v : OracleComp LeanXmss.HashSpec Digest)
        (WalkXQ p)
  | 0, _ => allQueriesSatisfy_pure _ _
  | levels + 1, v => by
    simp only [treeFold]
    refine allQueriesSatisfy_bind (walkX_treeFold p lay key path levels v) fun _ ↦ ?_
    split <;> exact walkX_tweakableHash _ _ _ (walkX_nodePayload _ _)

theorem walkX_layerRoot (p : PublicParameter) (lay : Layer) (key : KeyIndex) (msg : HashInput)
    (part : LayerSignature) :
    AllQueriesSatisfy (layerRoot p lay key msg part : OracleComp LeanXmss.HashSpec _)
      (WalkXQ p) := by
  unfold layerRoot
  refine allQueriesSatisfy_bind (walkX_otsLeaf _ _ _ _ _ _) fun o ↦ ?_
  rcases o with _ | leaf
  · exact allQueriesSatisfy_pure _ _
  · dsimp only
    have h1 := walkX_treeFold p lay key part.path layerHeight leaf
    generalize (treeFold p lay key part.path layerHeight leaf :
      OracleComp LeanXmss.HashSpec Digest) = X at h1 ⊢
    exact allQueriesSatisfy_bind h1 fun _ ↦ allQueriesSatisfy_pure _ _

/-- **Every query of leanXMSS's verification is a scheme input of the key's parameter, not shaped
as a derivation.** -/
theorem xmss_verify_queriesN (pk : PublicKey) (m : Message) (σ : Signature) :
    QueriesSat (Concrete.verify pk m σ : OracleComp LeanXmss.HashSpec Bool)
      (SchemeInputN (bytesLE 16 pk.parameter)) := by
  rw [queriesSat_iff]
  simp only [Concrete.verify]
  have hb := walkX_layerRoot pk.parameter bottomLayer (keyAt σ.leafIndex bottomLayer)
    (bytesLE 32 m) (σ.layers bottomLayer)
  generalize (layerRoot pk.parameter bottomLayer (keyAt σ.leafIndex bottomLayer) (bytesLE 32 m)
    (σ.layers bottomLayer) : OracleComp LeanXmss.HashSpec (Option Digest)) = X at hb ⊢
  refine allQueriesSatisfy_bind hb fun o ↦ ?_
  rcases o with _ | b
  · exact allQueriesSatisfy_pure _ _
  · dsimp only
    have ht := walkX_layerRoot pk.parameter topLayer (keyAt σ.leafIndex topLayer)
      (bytesLE 16 b) (σ.layers topLayer)
    generalize (layerRoot pk.parameter topLayer (keyAt σ.leafIndex topLayer) (bytesLE 16 b)
      (σ.layers topLayer) : OracleComp LeanXmss.HashSpec (Option Digest)) = Y at ht ⊢
    refine allQueriesSatisfy_bind ht fun o' ↦ ?_
    rcases o' with _ | r <;> exact allQueriesSatisfy_pure _ _

/-- **Every query of leanXMSS's verification is a scheme input of the key's parameter.** -/
theorem xmss_verify_queries (pk : PublicKey) (m : Message) (σ : Signature) :
    QueriesSat (Concrete.verify pk m σ : OracleComp LeanXmss.HashSpec Bool)
      (SchemeInput (bytesLE 16 pk.parameter)) :=
  (queriesSat_iff _ _).mpr (((queriesSat_iff _ _).mp (xmss_verify_queriesN pk m σ)).mono
    fun _ (h : SchemeInputN _ _) ↦ h.1)

/-! ### Key generation -/

/-- The seed hash `"leanXMSS" ‖ S0` is a derivation. -/
theorem xmss_seedHashInput_derivShape (s : MasterSeed) : DerivShape (seedHashInput s) :=
  Or.inl ⟨by simp [seedHashInput, seedTag, bytesLE], List.prefix_append _ _⟩

/-- The parameter derivation `0^16 ‖ A_param ‖ S` is a derivation. -/
theorem xmss_paramInput_derivShape (s : MasterSeed) :
    DerivShape (keygenHashInput 0 .parameter s) := by
  refine Or.inr (Or.inr ⟨by simp [keygenHashInput, fieldBytes, bytesLE], ?_⟩)
  have h : bytesLE 16 (0 : PublicParameter) = List.replicate 16 0 := by decide
  rw [keygenHashInput, h]
  exact List.prefix_append _ _

/-- Key generation, its two derivations made explicit: the tree under the derived parameter. -/
theorem xmss_keygenFromSeed_eq (seed : MasterSeed) :
    Seeded.keygenFromSeed seed =
      (liftM (LeanXmss.HashSpec.query (seedHashInput seed)) : OracleComp LeanXmss.HashSpec _) >>=
        fun s ↦ (liftM (LeanXmss.HashSpec.query (keygenHashInput 0 .parameter s)) :
          OracleComp LeanXmss.HashSpec _) >>= fun o ↦
          (Seeded.treeNode (truncateHash o) topLayer s layerHeight 0 :
            OracleComp LeanXmss.HashSpec Digest) >>= fun root ↦
            pure (⟨root, truncateHash o⟩, ⟨s, truncateHash o, root⟩) := by
  simp only [Seeded.keygenFromSeed, schemeSeed, deriveKey, oracleHash, bind_assoc, pure_bind]
  rfl

/-- **Key generation's queries**: on every logged run, each query is a derivation or a scheme input
of the output's parameter, not shaped as a derivation. -/
theorem xmss_keygen_queriesN (seed : MasterSeed) :
    ∀ z ∈ support ((simulateQ
        (QueryImpl.ofLift LeanXmss.HashSpec (OracleComp LeanXmss.HashSpec)).withLogging
        (Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1), DerivShape x ∨ SchemeInputN (bytesLE 16 z.1.2.parameter) x := by
  show ∀ z ∈ support ((simulateQ loggingOracle (Seeded.keygenFromSeed seed)).run), _
  intro z hz x hx
  rw [xmss_keygenFromSeed_eq] at hz
  -- the tree's height as a variable: a goal with a concrete tree node would be reduced
  generalize layerHeight = L at hz
  rw [run_simulateQ_loggingOracle_query_bind, support_bind] at hz
  simp only [Set.mem_iUnion, support_map] at hz
  obtain ⟨s, -, z1, hz1, rfl⟩ := hz
  rw [run_simulateQ_loggingOracle_query_bind, support_bind] at hz1
  simp only [Set.mem_iUnion, support_map] at hz1
  obtain ⟨o, -, z2, hz2, rfl⟩ := hz1
  have hall : AllQueriesSatisfy ((Seeded.treeNode (truncateHash o) topLayer s L 0 :
      OracleComp LeanXmss.HashSpec Digest) >>= fun root ↦
        (pure (⟨root, truncateHash o⟩, ⟨s, truncateHash o, root⟩) :
          OracleComp LeanXmss.HashSpec (PublicKey × Seeded.SecretKey))) (WalkXQ (truncateHash o)) :=
    allQueriesSatisfy_bind (walkX_treeNode _ _ _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _
  have hpar : z2.1.2.parameter = truncateHash o := by
    have h1 : z2.1 ∈ Prod.fst '' support _ := ⟨z2, hz2, rfl⟩
    rw [← support_map, loggingOracle.support_fst_map_run_simulateQ, mem_support_bind_iff] at h1
    obtain ⟨root, -, h⟩ := h1
    rw [mem_support_pure_iff] at h
    rw [h]
  simp only [List.map_cons, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | rfl | ⟨e, he, rfl⟩
  · exact Or.inl (xmss_seedHashInput_derivShape seed)
  · exact Or.inl (xmss_paramInput_derivShape s)
  · right
    dsimp only
    rw [hpar]
    exact holds_of_mem_log_of_mem_support_run_simulateQ hall hz2 e he

/-- **Key generation's queries** (the interface of P2d and P7): each query is a derivation or a
scheme input of the output's parameter. -/
theorem xmss_keygen_queries (seed : MasterSeed) :
    ∀ z ∈ support ((simulateQ
        (QueryImpl.ofLift LeanXmss.HashSpec (OracleComp LeanXmss.HashSpec)).withLogging
        (Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1), DerivShape x ∨ SchemeInput (bytesLE 16 z.1.2.parameter) x :=
  fun z hz x hx ↦ (xmss_keygen_queriesN seed z hz x hx).imp_right (·.1)

/-- **The keys carry the same parameter.** -/
theorem xmss_keygen_param (seed : MasterSeed) :
    ∀ z ∈ support (Seeded.keygenFromSeed seed), z.1.parameter = z.2.parameter := by
  intro z hz
  rw [xmss_keygenFromSeed_eq] at hz
  generalize layerHeight = L at hz
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨_, -, _, -, _, -, rfl⟩ := hz
  rfl

/-- **Key generation makes at most two queries shaped as derivations.** -/
theorem xmss_keygen_deriv_count (seed : MasterSeed) :
    IsQueryBoundP (Seeded.keygenFromSeed seed) DerivShapeQ 2 := by
  rw [xmss_keygenFromSeed_eq]
  generalize layerHeight = L
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by norm_num), fun s ↦ ?_⟩
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by split <;> norm_num), fun o ↦ ?_⟩
  refine walk_isQueryBoundP_of_all ?_ _
  exact (allQueriesSatisfy_bind (walkX_treeNode _ _ _ _ _) fun _ ↦
    allQueriesSatisfy_pure _ _).mono fun _ (h : SchemeInputN _ _) ↦ h.2

end Xmss

end
end LeanVM.E2E
