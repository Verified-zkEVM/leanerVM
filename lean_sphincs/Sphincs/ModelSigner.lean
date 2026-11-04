import Sphincs.Model

/-!
# Key generation and signing: the model's are the statement's

`Sphincs/Model.lean` for the other two algorithms: the model's key generation
(`FORS.Seeded.keygen`) and signer (`FORS.Seeded.sign`), their queries answered by Keccak-256 over
`π`, are the statement's (`simulateQ_keygen`, `simulateQ_sign`). The model's signer is written for
every shape: at this configuration every index lands in the kept part of the top tree
(`landed`), so its search over randomizers stops at the first, after one digest call, which the
statement's signer makes too; each tree's kept part is the whole tree (`keptHeight_eq`,
`keptPosition_eq`), so no surrogate node is derived; and its secret key's root is not hashed
(`sign_root`).
-/

open OracleComp OracleSpec

namespace Sphincs.Model

open HashSig HashSig.OverPermutation Common Common.SufCma

attribute [local instance] params

local notation "σ" => schemeHashOverPermutation

/-! ## The shape at this configuration -/

theorem keptHeight_eq (lay : FORS.Layer) : FORS.keptHeight lay = FORS.layerHeight lay := by
  fin_cases lay <;> rfl

theorem keptPosition_eq (parameter : FORS.PublicParameter) (lay : FORS.Layer) :
    FORS.keptPosition parameter lay = 0 := by
  unfold FORS.keptPosition FORS.subtreePosition
  split
  · exact Nat.mod_one _
  · rfl

theorem landed (parameter : FORS.PublicParameter) (index : FORS.Index) :
    FORS.Landed parameter index := by
  unfold FORS.Landed FORS.subtreePosition
  have := index.isLt
  change index.val < 2 ^ 26 at this
  change index.val / 2 ^ 26 = parameter.toNat % 2 ^ (26 - 26)
  rw [Nat.div_eq_of_lt this]
  exact (Nat.mod_one _).symm

theorem sim_ite {α : Type} (c : Prop) [Decidable c] (a b : OracleComp FORS.HashSpec α) :
    simulateQ σ (@ite (OracleComp FORS.HashSpec α) c _ a b) =
      if c then simulateQ σ a else simulateQ σ b := by
  split <;> rfl

theorem hashHalf_eq : @FORS.hashHalf = @hashHalfForChain := rfl

/-! ## Seed derivations -/

section Derivations

variable (seed : FORS.MasterSeed)

theorem simulateQ_deriveKey_parameter (parameter : FORS.PublicParameter) :
    simulateQ σ (FORS.deriveKey (m := OracleComp FORS.HashSpec) parameter .parameter seed) =
      th queryPermutation parameter (keygenDomainFields .parameter) (littleEndianBytes 32 seed) := by
  simp only [FORS.deriveKey, sim_bind, sim_pure, simulateQ_oracleHash, th]
  rfl

theorem simulateQ_deriveOutput_ots (parameter : FORS.PublicParameter) (lay : FORS.Layer)
    (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex) (pair : FORS.ChainPair) :
    simulateQ σ (FORS.deriveOutput (m := OracleComp FORS.HashSpec) parameter (.ots lay tree leaf pair)
      seed) =
      thPair queryPermutation parameter
        (keygenDomainFields (.oneTimeChainPair (toLayer lay) tree leaf pair))
        (littleEndianBytes 32 seed) := by
  simp only [FORS.deriveOutput, simulateQ_oracleHash, thPair]
  congr 1

theorem simulateQ_deriveOutput_fors (parameter : FORS.PublicParameter) (index : FORS.Index)
    (forsTree : FORS.FTree) (pair : FORS.FPair) :
    simulateQ σ (FORS.deriveOutput (m := OracleComp FORS.HashSpec) parameter (.fors index forsTree pair)
      seed) =
      thPair queryPermutation parameter (keygenDomainFields (.forsSecretPair index forsTree pair))
        (littleEndianBytes 32 seed) := by
  simp only [FORS.deriveOutput, simulateQ_oracleHash, thPair]
  rfl

theorem simulateQ_schemeSeed :
    simulateQ σ (FORS.schemeSeed (m := OracleComp FORS.HashSpec) seed) =
      taggedSeed queryPermutation seedTag seed := by
  rw [FORS.schemeSeed]
  exact simulateQ_oracleHash _

end Derivations

/-! ## One-time keys and the hypertree -/

section Hypertree

open Verification KeyGenerationAndSigning

variable (parameter : FORS.PublicParameter) (seed : FORS.MasterSeed)

theorem simulateQ_otsSecrets (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex) :
    simulateQ σ (FORS.Seeded.otsSecrets (m := OracleComp FORS.HashSpec) parameter lay tree leaf
      seed) = otsSecrets queryPermutation parameter (toLayer lay) tree leaf seed := by
  simp only [FORS.Seeded.otsSecrets, otsSecrets, sim_bind, sim_pure, simulateQ_sequenceFin,
    simulateQ_deriveOutput_ots]
  rfl

theorem simulateQ_oneTimePublicKey (lay : FORS.Layer) (tree : FORS.TreeIndex)
    (leaf : FORS.LeafIndex) :
    simulateQ σ (FORS.Seeded.oneTimePublicKey (m := OracleComp FORS.HashSpec) parameter lay tree
      leaf seed) = oneTimePublicKey queryPermutation parameter (toLayer lay) tree leaf seed := by
  simp only [FORS.Seeded.oneTimePublicKey, oneTimePublicKey, sim_bind, simulateQ_otsSecrets,
    simulateQ_sequenceFin, simulateQ_chainWalk]
  rfl

theorem simulateQ_otsSignFrom (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (message : FORS.HashInput) :
    ∀ (attempts counter : ℕ),
      simulateQ σ (FORS.Seeded.otsSignFrom (m := OracleComp FORS.HashSpec) parameter lay tree leaf
        seed message attempts counter) =
        otsSignFrom queryPermutation parameter (toLayer lay) tree leaf seed message attempts counter
  | 0, _ => by
    simp only [FORS.Seeded.otsSignFrom, otsSignFrom]
    exact sim_pure _
  | attempts + 1, counter => by
    simp only [FORS.Seeded.otsSignFrom, otsSignFrom, sim_bind, simulateQ_encode]
    refine bind_eq_of rfl fun found ↦ ?_
    rcases found with _ | encoding
    · exact simulateQ_otsSignFrom lay tree leaf message attempts (counter + 1)
    · simp only [sim_bind, sim_pure, simulateQ_otsSecrets, simulateQ_sequenceFin, simulateQ_chainWalk]
      rfl

theorem simulateQ_otsSign (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (message : FORS.HashInput) :
    simulateQ σ (FORS.Seeded.otsSign (m := OracleComp FORS.HashSpec) parameter lay tree leaf seed
      message) = otsSign queryPermutation parameter (toLayer lay) tree leaf seed message :=
  simulateQ_otsSignFrom parameter seed lay tree leaf message _ _

theorem simulateQ_treeNode (lay : FORS.Layer) (tree : FORS.TreeIndex) :
    ∀ (level nodeIndex : ℕ),
      simulateQ σ (FORS.Seeded.treeNode (m := OracleComp FORS.HashSpec) parameter lay tree seed
        level nodeIndex) = treeNode queryPermutation parameter (toLayer lay) tree seed level nodeIndex
  | 0, nodeIndex => by
    simp only [FORS.Seeded.treeNode, treeNode, buildTree, sim_bind, simulateQ_oneTimePublicKey,
      simulateQ_leafHash]
    rfl
  | level + 1, nodeIndex => by
    simp only [FORS.Seeded.treeNode, sim_bind, simulateQ_treeNode lay tree level,
      simulateQ_tweakableHash]
    rfl

theorem simulateQ_treeRoot (lay : FORS.Layer) (tree : FORS.TreeIndex) :
    simulateQ σ (FORS.Seeded.treeRoot (m := OracleComp FORS.HashSpec) parameter lay tree seed) =
      treeNode queryPermutation parameter (toLayer lay) tree seed (FORS.layerHeight lay) 0 := by
  simp only [FORS.Seeded.treeRoot, keptHeight_eq, Nat.sub_self, FORS.Seeded.spineNode,
    keptPosition_eq, simulateQ_treeNode]
  rfl

/-- `simulateQ_treeRoot` at a parameter derived as a digest, as key generation derives it. -/
theorem simulateQ_treeRoot_digest (parameter : FORS.Digest) (lay : FORS.Layer) (tree : FORS.TreeIndex) :
    simulateQ σ (FORS.Seeded.treeRoot (m := OracleComp FORS.HashSpec) parameter lay tree seed) =
      treeNode queryPermutation parameter (toLayer lay) tree seed (FORS.layerHeight lay) 0 :=
  simulateQ_treeRoot parameter seed lay tree

theorem simulateQ_treePath (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex) :
    simulateQ σ (FORS.Seeded.treePath (m := OracleComp FORS.HashSpec) parameter lay tree seed leaf) =
      sequenceFin fun level : Fin (FORS.layerHeight lay) ↦
        treeNode queryPermutation parameter (toLayer lay) tree seed level.val
          (Nat.xor (leaf.val / 2 ^ level.val) 1) := by
  simp only [FORS.Seeded.treePath, simulateQ_sequenceFin, keptHeight_eq, Fin.is_lt, ↓reduceIte,
    simulateQ_treeNode]
  rfl

/-- `simulateQ_treePath` at the statement's tree and leaf types. -/
theorem simulateQ_treePath_statement (lay : FORS.Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) :
    simulateQ σ (FORS.Seeded.treePath (m := OracleComp FORS.HashSpec) parameter lay tree seed leaf) =
      sequenceFin fun level : Fin (FORS.layerHeight lay) ↦
        treeNode queryPermutation parameter (toLayer lay) tree seed level.val
          (Nat.xor (leaf.val / 2 ^ level.val) 1) :=
  simulateQ_treePath parameter seed lay tree leaf

end Hypertree

/-! ## FORS -/

section Fors

open Verification KeyGenerationAndSigning

variable (parameter : FORS.PublicParameter) (index : FORS.Index) (forsTree : FORS.FTree)
  (seed : FORS.MasterSeed)

theorem simulateQ_forsSecret (leaf : FORS.FLeaf) :
    simulateQ σ (FORS.Seeded.forsSecret (m := OracleComp FORS.HashSpec) parameter index forsTree
      leaf seed) = forsSecret queryPermutation parameter index forsTree leaf seed := by
  simp only [FORS.Seeded.forsSecret, forsSecret, sim_bind, sim_pure, simulateQ_deriveOutput_fors]
  rfl

theorem simulateQ_forsNode :
    ∀ (level node : ℕ),
      simulateQ σ (FORS.Seeded.forsNode (m := OracleComp FORS.HashSpec) parameter index forsTree
        seed level node) = forsNode queryPermutation parameter index forsTree seed level node
  | 0, node => by
    simp only [FORS.Seeded.forsNode, forsNode, sim_bind, simulateQ_forsSecret,
      FORS.Concrete.forsLeafHash, simulateQ_tweakableHash]
    rfl
  | 1, node => by
    simp only [FORS.Seeded.forsNode, forsNode, sim_bind, simulateQ_deriveOutput_fors,
      FORS.Concrete.forsLeafHash, simulateQ_tweakableHash]
    rfl
  | level + 2, node => by
    simp only [FORS.Seeded.forsNode, forsNode, sim_bind, simulateQ_forsNode (level + 1)]
    refine bind_eq_of rfl fun left ↦ bind_eq_of rfl fun right ↦ ?_
    by_cases hlevel : level + 1 < 10
    · rw [dite_eq_left (show level + 1 < FORS.forsHeight from hlevel),
        dite_eq_left (show level + 1 < forsTreeHeight from hlevel), simulateQ_tweakableHash]
      rfl
    · rw [dite_eq_right (show ¬level + 1 < FORS.forsHeight from hlevel),
        dite_eq_right (show ¬level + 1 < forsTreeHeight from hlevel), sim_pure]
      rfl

theorem simulateQ_forsKey :
    simulateQ σ (FORS.Seeded.forsKey (m := OracleComp FORS.HashSpec) parameter index seed) =
      forsKey queryPermutation parameter index seed := by
  simp only [FORS.Seeded.forsKey, forsKey, simulateQ_sequenceFin, sim_bind, sim_pure,
    simulateQ_forsNode]
  rfl

theorem simulateQ_forsTreeOpen (leaf : FORS.FLeaf) :
    Functor.map ofModelTreeOpening (simulateQ σ (FORS.Seeded.treeOpen
      (m := OracleComp FORS.HashSpec) parameter index forsTree leaf seed)) =
      forsTreeOpen queryPermutation parameter index forsTree leaf seed := by
  simp only [FORS.Seeded.treeOpen, sim_bind, sim_pure, simulateQ_deriveOutput_fors,
    FORS.Concrete.forsLeafHash, simulateQ_tweakableHash, simulateQ_sequenceFin, sim_ite,
    simulateQ_forsNode]
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun output ↦ ?_)
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun siblingLeaf ↦ ?_)
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun path ↦ ?_)
  exact map_pure _ _

theorem simulateQ_forsOpen (leaves : FORS.FTree → FORS.FLeaf) :
    (fun opening forsTree ↦ ofModelTreeOpening (opening forsTree)) <$>
      simulateQ σ (FORS.Seeded.forsOpen (m := OracleComp FORS.HashSpec) parameter index leaves
        seed) = forsOpen queryPermutation parameter index leaves seed := by
  simp only [FORS.Seeded.forsOpen, simulateQ_sequenceFin]
  exact (sequenceFin_map ofModelTreeOpening _ _).symm.trans
    (congrArg _ (funext fun forsTree ↦ simulateQ_forsTreeOpen parameter index forsTree seed
      (leaves forsTree)))

end Fors

/-! ## Key generation -/

/-- A model secret key as the statement's: its root, which the signer does not hash, dropped. -/
def toStatementSecretKey (secretKey : FORS.Seeded.SecretKey) : SecretKey :=
  ⟨secretKey.seed, secretKey.parameter⟩

/-- The model's keys as the statement's. -/
def ofModelKeys (keys : FORS.PublicKey × FORS.Seeded.SecretKey) : PublicKey × SecretKey :=
  (ofModelPublicKey keys.1, toStatementSecretKey keys.2)

theorem simulateQ_keygen (seed : FORS.MasterSeed) :
    ofModelKeys <$> simulateQ σ (FORS.Seeded.keygen seed) =
      KeyGenerationAndSigning.keygenFromSeed queryPermutation seed := by
  simp only [FORS.Seeded.keygen, FORS.Seeded.keygenFromSeed, sim_bind, sim_pure,
    simulateQ_schemeSeed, simulateQ_deriveKey_parameter, simulateQ_treeRoot_digest]
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun schemeSeed ↦ ?_)
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun parameter ↦ ?_)
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun root ↦ ?_)
  exact map_pure _ _

/-! ## The layers' messages and signatures -/

section Layers

open Verification KeyGenerationAndSigning

theorem childTree_top (index : FORS.Index) :
    FORS.Concrete.childTree ⟨0, by decide⟩ (FORS.Concrete.treeIndexAt index ⟨0, by decide⟩)
      (FORS.Concrete.leafIndexAt index ⟨0, by decide⟩) = treeOfIndex ⟨1, by decide⟩ index := by
  have := index.isLt
  change index.val < 67108864 at this
  apply Fin.ext
  show (index.val / 67108864 * 1024 + index.val / 65536 % 1024) % 67108864 = index.val / 65536
  omega

theorem childTree_middle (index : FORS.Index) :
    FORS.Concrete.childTree ⟨1, by decide⟩ (FORS.Concrete.treeIndexAt index ⟨1, by decide⟩)
      (FORS.Concrete.leafIndexAt index ⟨1, by decide⟩) = treeOfIndex ⟨0, by decide⟩ index := by
  have := index.isLt
  change index.val < 67108864 at this
  apply Fin.ext
  show (index.val / 65536 * 256 + index.val / 256 % 256) % 67108864 = index.val / 256
  omega

theorem childTree_bottom (index : FORS.Index) :
    FORS.Concrete.childTree ⟨2, by decide⟩ (FORS.Concrete.treeIndexAt index ⟨2, by decide⟩)
      (FORS.Concrete.leafIndexAt index ⟨2, by decide⟩) = index := by
  have := index.isLt
  change index.val < 67108864 at this
  apply Fin.ext
  show (index.val / 256 * 256 + index.val / 1 % 256) % 67108864 = index.val
  omega

theorem simulateQ_layerMessage (secretKey : FORS.Seeded.SecretKey) (index : FORS.Index)
    (lay : FORS.Layer) :
    simulateQ σ (FORS.Seeded.layerMessage (m := OracleComp FORS.HashSpec) secretKey index lay) =
      layerMessage queryPermutation secretKey.parameter secretKey.seed (toLayer lay) index := by
  fin_cases lay
  · simp only [FORS.Seeded.layerMessage, FORS.Seeded.keyMessage]
    rw [dite_eq_left (show (0 : ℕ) + 1 < FORS.numLayers by decide), sim_bind, simulateQ_treeRoot,
      childTree_top]
    unfold layerMessage
    rw [dite_eq_right (show ¬(toLayer ⟨0, by decide⟩).val = 0 by decide)]
    exact bind_eq_of rfl fun root ↦ sim_pure _
  · simp only [FORS.Seeded.layerMessage, FORS.Seeded.keyMessage]
    rw [dite_eq_left (show (1 : ℕ) + 1 < FORS.numLayers by decide), sim_bind, simulateQ_treeRoot,
      childTree_middle]
    unfold layerMessage
    rw [dite_eq_right (show ¬(toLayer ⟨1, by decide⟩).val = 0 by decide)]
    exact bind_eq_of rfl fun root ↦ sim_pure _
  · simp only [FORS.Seeded.layerMessage, FORS.Seeded.keyMessage]
    rw [dite_eq_right (show ¬(2 : ℕ) + 1 < FORS.numLayers by decide), childTree_bottom, sim_bind,
      simulateQ_forsKey]
    unfold layerMessage
    rw [dite_eq_left (show (toLayer ⟨2, by decide⟩).val = 0 from rfl)]
    exact bind_eq_of rfl fun key ↦ sim_pure _

/-- A model layer signature as the statement's: its path read through its length's equality. -/
def ofModelLayerSignature (lay : FORS.Layer) (layerSignature : FORS.LayerSignature lay) :
    LayerSignature (toLayer lay) :=
  ⟨layerSignature.counter, layerSignature.chainValues,
    fun level ↦ layerSignature.path (Fin.cast (layerHeight_toLayer lay) level)⟩

/-- A `sequenceFin` over `Fin n'`, through an equality `n = n'`, then a continuation. -/
theorem sequenceFin_cast {m : Type → Type} [Monad m] {α β : Type} {n n' : ℕ} (h : n = n')
    (g : Fin n' → m α) (k : (Fin n' → α) → m β) :
    sequenceFin g >>= k = sequenceFin (fun i ↦ g (Fin.cast h i)) >>= fun v ↦ k (fun i ↦ v (Fin.cast h.symm i)) := by
  subst h
  rfl

theorem simulateQ_signLayer (secretKey : FORS.Seeded.SecretKey) (index : FORS.Index)
    (lay : FORS.Layer) :
    Option.map (ofModelLayerSignature lay) <$>
      simulateQ σ (FORS.Seeded.signLayer (m := OracleComp FORS.HashSpec) secretKey index lay) =
      signLayer queryPermutation (toStatementSecretKey secretKey) index (toLayer lay) := by
  simp only [FORS.Seeded.signLayer, sim_bind, simulateQ_layerMessage, simulateQ_otsSign]
  rw [treeIndexAt_eq, leafIndexAt_eq]
  unfold signLayer
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun message ↦ ?_)
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun found ↦ ?_)
  rcases found with _ | ⟨counter, values⟩
  · exact (congrArg _ (sim_pure _)).trans (map_pure _ _)
  · rw [sim_bind, simulateQ_treePath_statement]
    unfold treePath
    dsimp only
    rw [sequenceFin_cast (layerHeight_toLayer lay).symm]
    refine (map_bind _ _ _).trans (bind_eq_of rfl fun path ↦ ?_)
    exact (congrArg _ (sim_pure _)).trans (map_pure _ _)

end Layers

/-! ## Signing -/

section Signing

open Verification KeyGenerationAndSigning

/-- The model's layered loop of three layers, flattened: each layer's signature, top first, then the
continuation on the three. -/
theorem sequenceLayers_bind {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type}
    (c : (lay : FORS.Layer) → m (Option (FORS.LayerSignature lay)))
    (k : Option ((lay : FORS.Layer) → FORS.LayerSignature lay) → m (Option β))
    (hk : k none = pure none) :
    FORS.Concrete.sequenceLayers c >>= k =
    (do
      let some top ← c ⟨0, by decide⟩ | return none
      let some middle ← c ⟨1, by decide⟩ | return none
      let some bottom ← c ⟨2, by decide⟩ | return none
      k (some (Fin.cases top (Fin.cases middle (Fin.cases bottom fun i ↦ Fin.elim0 i))))) := by
  simp only [FORS.Concrete.sequenceLayers, FORS.Concrete.sequenceDep, bind_assoc]
  refine bind_congr fun r0 ↦ ?_
  rcases r0 with _ | top
  · simp [hk]
  · simp only [bind_assoc]
    refine bind_congr fun r1 ↦ ?_
    rcases r1 with _ | middle
    · simp [hk]
    · simp only [bind_assoc]
      refine bind_congr fun r2 ↦ ?_
      rcases r2 with _ | bottom
      · simp [hk]
      · simp

theorem signDigestLoop_succ (secretKey : FORS.Seeded.SecretKey) (message : FORS.Message)
    (step randomness : FORS.Randomness) (attempts : ℕ) :
    FORS.Seeded.signDigestLoop (m := OracleComp FORS.HashSpec) secretKey message step (attempts + 1)
      randomness =
      (fun first ↦ some (randomness, FORS.Concrete.blockIndex first)) <$>
        FORS.Concrete.messageDigestCall secretKey.parameter secretKey.root message randomness
          FORS.firstCall := by
  simp only [FORS.Seeded.signDigestLoop, FORS.Seeded.signAttempt, landed, ↓reduceIte, bind_pure_comp,
    bind_map_left]

theorem randomizerHashInput_eq (parameter : FORS.PublicParameter) (seed : FORS.MasterSeed)
    (message : FORS.Message) :
    FORS.randomizerHashInput parameter seed message =
      thInput parameter (tweakFields 7 0 0 0) (littleEndianBytes 32 seed ++ littleEndianBytes 32 message) :=
  List.append_assoc _ _ _

theorem simulateQ_deriveRandomizer (parameter : FORS.PublicParameter) (seed : FORS.MasterSeed)
    (message : FORS.Message) :
    simulateQ σ (FORS.deriveRandomizer (m := OracleComp FORS.HashSpec) parameter seed message) =
      keccakHash queryPermutation (FORS.randomizerHashInput parameter seed message) >>= fun output ↦
        pure (FORS.truncateHash output, FORS.walkStep (FORS.upperHash output)) := by
  simp only [FORS.deriveRandomizer, sim_bind, sim_pure, simulateQ_oracleHash]
  rfl

/-- The model's layer signatures as the statement's, bottom first. -/
theorem ofModelSignature_layers (randomness : FORS.Randomness)
    (opening : FORS.FTree → FORS.TreeOpening) (top : FORS.LayerSignature ⟨0, by decide⟩)
    (middle : FORS.LayerSignature ⟨1, by decide⟩) (bottom : FORS.LayerSignature ⟨2, by decide⟩) :
    ofModelSignature ⟨randomness, opening,
      Fin.cases top (Fin.cases middle (Fin.cases bottom fun i ↦ Fin.elim0 i))⟩ =
      ⟨randomness, fun forsTree ↦ ofModelTreeOpening (opening forsTree),
        layerSignatures (ofModelLayerSignature ⟨2, by decide⟩ bottom)
          (ofModelLayerSignature ⟨1, by decide⟩ middle) (ofModelLayerSignature ⟨0, by decide⟩ top)⟩ := by
  simp only [ofModelSignature]
  congr 1
  funext layer
  fin_cases layer <;> rfl

theorem signLayer_top (secretKey : FORS.Seeded.SecretKey) (index : Index) :
    signLayer queryPermutation (toStatementSecretKey secretKey) index 2 =
      Option.map (ofModelLayerSignature ⟨0, by decide⟩) <$>
        simulateQ σ (FORS.Seeded.signLayer (m := OracleComp FORS.HashSpec) secretKey index ⟨0, by decide⟩) :=
  (simulateQ_signLayer secretKey index ⟨0, by decide⟩).symm

theorem signLayer_middle (secretKey : FORS.Seeded.SecretKey) (index : Index) :
    signLayer queryPermutation (toStatementSecretKey secretKey) index 1 =
      Option.map (ofModelLayerSignature ⟨1, by decide⟩) <$>
        simulateQ σ (FORS.Seeded.signLayer (m := OracleComp FORS.HashSpec) secretKey index ⟨1, by decide⟩) :=
  (simulateQ_signLayer secretKey index ⟨1, by decide⟩).symm

theorem signLayer_bottom (secretKey : FORS.Seeded.SecretKey) (index : Index) :
    signLayer queryPermutation (toStatementSecretKey secretKey) index 0 =
      Option.map (ofModelLayerSignature ⟨2, by decide⟩) <$>
        simulateQ σ (FORS.Seeded.signLayer (m := OracleComp FORS.HashSpec) secretKey index ⟨2, by decide⟩) :=
  (simulateQ_signLayer secretKey index ⟨2, by decide⟩).symm

theorem forsOpen_eq (parameter : PublicParameter) (index : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (seed : MasterSeed) :
    forsOpen queryPermutation parameter index leaves seed =
      (fun opening forsTree ↦ ofModelTreeOpening (opening forsTree)) <$>
        simulateQ σ (FORS.Seeded.forsOpen (m := OracleComp FORS.HashSpec) parameter index leaves seed) :=
  (simulateQ_forsOpen parameter index seed leaves).symm

theorem simulateQ_sign (secretKey : FORS.Seeded.SecretKey) (message : FORS.Message) :
    Option.map ofModelSignature <$>
      simulateQ σ (FORS.Seeded.sign (m := OracleComp FORS.HashSpec) secretKey message) =
      sign queryPermutation (toStatementSecretKey secretKey) message := by
  rw [FORS.Seeded.sign, sim_bind, simulateQ_deriveRandomizer, bind_assoc]
  unfold sign
  simp only [th, bind_assoc, pure_bind]
  rw [randomizerHashInput_eq]
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun output ↦ ?_)
  rw [show FORS.digestAttemptLimit = (2 ^ 32 - 1) + 1 from rfl, sim_bind,
    signDigestLoop_succ, sim_map, simulateQ_messageDigestCall]
  refine (congrArg _ (bind_map_left _ _ _)).trans ?_
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun first ↦ ?_)
  dsimp only
  rw [sim_bind, simulateQ_messageDigest]
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun digest ↦ ?_)
  rw [sim_bind, forsOpen_eq]
  refine (map_bind _ _ _).trans (Eq.trans ?_ (bind_map_left _ _ _).symm)
  refine bind_eq_of rfl fun opening ↦ ?_
  rw [sequenceLayers_bind _ _ (by rfl)]
  rw [signLayer_top, signLayer_middle, signLayer_bottom, sim_bind]
  refine (map_bind _ _ _).trans (Eq.trans ?_ (bind_map_left _ _ _).symm)
  refine bind_eq_of rfl fun r0 ↦ ?_
  rcases r0 with _ | top
  · exact (congrArg _ (sim_pure _)).trans (map_pure _ _)
  dsimp only
  rw [sim_bind]
  refine (map_bind _ _ _).trans (Eq.trans ?_ (bind_map_left _ _ _).symm)
  refine bind_eq_of rfl fun r1 ↦ ?_
  rcases r1 with _ | middle
  · exact (congrArg _ (sim_pure _)).trans (map_pure _ _)
  dsimp only
  rw [sim_bind]
  refine (map_bind _ _ _).trans (Eq.trans ?_ (bind_map_left _ _ _).symm)
  refine bind_eq_of rfl fun r2 ↦ ?_
  rcases r2 with _ | bottom
  · exact (congrArg _ (sim_pure _)).trans (map_pure _ _)
  dsimp only
  refine (congrArg _ (sim_pure _)).trans ((map_pure _ _).trans ?_)
  rw [Option.map_some, ofModelSignature_layers]
  rfl

end Signing

end Sphincs.Model
