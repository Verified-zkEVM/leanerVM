import Sphincs.Model

/-!
# Key generation and signing: the model's are the statement's

`Sphincs/Model.lean` for the other two algorithms: the model's key generation
(`FORS.Seeded.keygen`) and signer, their queries answered by Keccak-256 over `π`, are the
statement's (`simulateQ_keygen`, `simulateQ_sign`). Both take the crate's secret key, the seed
`S0`: the model's key generation keeps it (`ofModelKeys`), and its signer derives the scheme seed
and the parameter from it (`deriveSeeded`) and signs with `FORS.Seeded.sign`, the crate's signer,
whose trees and FORS trees are built once (`simulateQ_treeNodeWithPath`, `simulateQ_forsOpenOnce`)
and whose layers run from the bottom up, as the statement's do. At this configuration each tree's
kept part is the whole tree (`keptHeight_eq`, `keptPosition_eq`), and the secret key's root is not
hashed (`sign_root`).
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


/-! ## The crate's signer: trees and FORS built once -/

section Once

open Verification KeyGenerationAndSigning

variable (parameter : FORS.PublicParameter) (seed : FORS.MasterSeed)

theorem simulateQ_treeNodeWithPath (lay : FORS.Layer) (tree : FORS.TreeIndex)
    (leaf : TreeLeafIndex) : ∀ (level nodeIndex : ℕ),
      simulateQ σ (FORS.Seeded.treeNodeWithPath (m := OracleComp FORS.HashSpec) parameter lay tree
        seed leaf.val level nodeIndex) =
        treeNodeWithPath queryPermutation parameter (toLayer lay) tree seed leaf level nodeIndex
  | 0, nodeIndex => by
    simp only [FORS.Seeded.treeNodeWithPath, treeNodeWithPath, buildTreeWithPath, sim_bind,
      sim_pure, simulateQ_oneTimePublicKey, simulateQ_leafHash, bind_assoc]
    rfl
  | level + 1, nodeIndex => by
    simp only [FORS.Seeded.treeNodeWithPath, sim_bind, sim_pure,
      simulateQ_treeNodeWithPath lay tree leaf level, simulateQ_tweakableHash]
    rfl

variable (index : FORS.Index) (forsTree : FORS.FTree)

theorem simulateQ_forsSubtree (leaf : FORS.FLeaf) : ∀ (height node : ℕ),
    simulateQ σ (FORS.Seeded.forsSubtree (m := OracleComp FORS.HashSpec) parameter index forsTree
      seed leaf height node) = forsSubtree queryPermutation parameter index forsTree seed leaf height node
  | 0, node => by
    simp only [FORS.Seeded.forsSubtree, forsSubtree, sim_bind, sim_pure,
      simulateQ_deriveOutput_fors, FORS.Concrete.forsLeafHash, simulateQ_tweakableHash]
    rfl
  | height + 1, node => by
    simp only [FORS.Seeded.forsSubtree, forsSubtree, sim_bind, sim_pure,
      simulateQ_forsSubtree leaf height]
    refine bind_eq_of rfl fun left ↦ bind_eq_of rfl fun right ↦ ?_
    by_cases hheight : height + 1 < 10
    · rw [dite_eq_left (show height + 1 < FORS.forsHeight from hheight),
        dite_eq_left (show height + 1 < forsTreeHeight from hheight), simulateQ_tweakableHash]
      rfl
    · rw [dite_eq_right (show ¬height + 1 < FORS.forsHeight from hheight),
        dite_eq_right (show ¬height + 1 < forsTreeHeight from hheight), sim_pure]
      rfl

theorem simulateQ_treeOpenOnce (leaf : FORS.FLeaf) :
    (fun r ↦ (r.1, ofModelTreeOpening r.2)) <$> simulateQ σ (FORS.Seeded.treeOpenOnce
      (m := OracleComp FORS.HashSpec) parameter index forsTree leaf seed) =
      forsTreeOpen queryPermutation parameter index forsTree leaf seed := by
  simp only [FORS.Seeded.treeOpenOnce, forsTreeOpen, sim_bind, sim_pure, simulateQ_forsSubtree]
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun left ↦ ?_)
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun right ↦ ?_)
  exact map_pure _ _

theorem simulateQ_forsOpenOnce (leaves : FORS.FTree → FORS.FLeaf) :
    (fun r ↦ (r.1, fun forsTree ↦ ofModelTreeOpening (r.2 forsTree))) <$>
      simulateQ σ (FORS.Seeded.forsOpenOnce (m := OracleComp FORS.HashSpec) parameter index leaves
        seed) = forsOpen queryPermutation parameter index leaves seed := by
  simp only [FORS.Seeded.forsOpenOnce, forsOpen, sim_bind, sim_pure, simulateQ_sequenceFin]
  have h : (fun forsTree ↦ forsTreeOpen queryPermutation parameter index forsTree (leaves forsTree)
      seed) = fun forsTree ↦ (fun r ↦ (r.1, ofModelTreeOpening r.2)) <$> simulateQ σ
        (FORS.Seeded.treeOpenOnce (m := OracleComp FORS.HashSpec) parameter index forsTree
          (leaves forsTree) seed) :=
    funext fun forsTree ↦ (simulateQ_treeOpenOnce parameter seed index forsTree (leaves forsTree)).symm
  rw [h]
  erw [sequenceFin_map]
  rw [bind_map_left, map_bind]
  exact bind_eq_of rfl fun trees ↦ map_pure _ _

end Once

/-! ## Key generation -/

/-- The model's public key as the statement's. -/
def ofModelKeys (keys : FORS.PublicKey × MasterSeed) : PublicKey × SecretKey :=
  (ofModelPublicKey keys.1, keys.2)

/-- What the model's key generation derives from the seed first: the scheme seed and the
parameter. -/
def deriveSeeded (seed : FORS.MasterSeed) :
    OracleComp FORS.HashSpec (FORS.MasterSeed × FORS.PublicParameter) := do
  let schemeSeed ← FORS.schemeSeed seed
  let parameter ← FORS.deriveKey 0 .parameter schemeSeed
  return (schemeSeed, parameter)

/-- The rest of the model's key generation: the top tree's root. -/
def keygenRest (derived : FORS.MasterSeed × FORS.PublicParameter) :
    OracleComp FORS.HashSpec (FORS.PublicKey × FORS.Seeded.SecretKey) := do
  let root ← FORS.Seeded.treeRoot derived.2 FORS.topLayer FORS.Concrete.rootTree derived.1
  return (⟨root, derived.2⟩, ⟨derived.1, derived.2, root⟩)

theorem simulateQ_deriveSeeded (seed : FORS.MasterSeed) :
    simulateQ σ (deriveSeeded seed) = (do
      let schemeSeed ← taggedSeed queryPermutation seedTag seed
      let parameter ← th queryPermutation 0 (keygenDomainFields .parameter)
        (littleEndianBytes 32 schemeSeed)
      return (schemeSeed, parameter)) := by
  simp only [deriveSeeded, sim_bind, sim_pure, simulateQ_schemeSeed, simulateQ_deriveKey_parameter]
  rfl

theorem keygen_eq (seed : FORS.MasterSeed) :
    FORS.Seeded.keygen seed = deriveSeeded seed >>= keygenRest := by
  simp only [FORS.Seeded.keygen, FORS.Seeded.keygenFromSeed, deriveSeeded, keygenRest, bind_assoc,
    pure_bind]

theorem simulateQ_keygen (seed : FORS.MasterSeed) :
    (fun keys ↦ (ofModelPublicKey keys.1, seed)) <$>
      simulateQ σ (FORS.Seeded.keygen seed : OracleComp FORS.HashSpec _) =
      KeyGenerationAndSigning.keygenFromSeed queryPermutation seed := by
  simp only [FORS.Seeded.keygen, FORS.Seeded.keygenFromSeed, sim_bind, sim_pure,
    simulateQ_schemeSeed, simulateQ_deriveKey_parameter, simulateQ_treeRoot_digest,
    KeyGenerationAndSigning.keygenFromSeed, KeyGenerationAndSigning.publicKeyOf, bind_assoc,
    pure_bind]
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun schemeSeed ↦ ?_)
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun parameter ↦ ?_)
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun root ↦ ?_)
  exact map_pure _ _

/-! ## Signing -/

section Signing

open Verification KeyGenerationAndSigning

/-- The crate signer's root is not hashed: the digest's payload is `m ‖ ρ`. -/
theorem sign_root (schemeSeed : FORS.MasterSeed) (parameter : FORS.PublicParameter)
    (root : FORS.Digest) (message : FORS.Message) :
    FORS.Seeded.sign (m := OracleComp FORS.HashSpec) ⟨schemeSeed, parameter, root⟩ message =
      FORS.Seeded.sign (m := OracleComp FORS.HashSpec) ⟨schemeSeed, parameter, 0⟩ message := rfl

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

/-- One layer of the crate's signer: the model's one-time signature and tree, at the statement's
layer `toLayer lay`. -/
theorem simulateQ_layerOtsSign (parameter : FORS.PublicParameter) (seed : FORS.MasterSeed)
    (index : FORS.Index) (lay : FORS.Layer) (message : FORS.HashInput) :
    simulateQ σ (FORS.Seeded.otsSign (m := OracleComp FORS.HashSpec) parameter lay
      (FORS.Concrete.treeIndexAt index lay) (FORS.Concrete.leafIndexAt index lay) seed message) =
      otsSign queryPermutation parameter (toLayer lay) (treeOfIndex (toLayer lay) index)
        (leafOfIndex (toLayer lay) index) seed message := by
  rw [simulateQ_otsSign, treeIndexAt_eq, leafIndexAt_eq]

theorem simulateQ_layerTree (parameter : FORS.PublicParameter) (seed : FORS.MasterSeed)
    (index : FORS.Index) (lay : FORS.Layer) :
    simulateQ σ (FORS.Seeded.treeNodeWithPath (m := OracleComp FORS.HashSpec) parameter lay
      (FORS.Concrete.treeIndexAt index lay) seed (FORS.Concrete.leafIndexAt index lay).val
      (FORS.layerHeight lay) 0) =
      treeNodeWithPath queryPermutation parameter (toLayer lay) (treeOfIndex (toLayer lay) index)
        seed (leafOfIndex (toLayer lay) index) (layerHeight (toLayer lay)) 0 := by
  rw [treeIndexAt_eq, leafIndexAt_eq, layerHeight_toLayer]
  exact simulateQ_treeNodeWithPath parameter seed lay _ _ _ _

/-- The three layers' data of the crate's signer as the statement's signature. -/
theorem ofModelSignature_layersOfData (randomness : FORS.Randomness)
    (opening : FORS.FTree → FORS.TreeOpening) (bottom middle top : FORS.Seeded.LayerData) :
    ofModelSignature ⟨randomness, opening, FORS.Seeded.layersOfData
      (Function.update (Function.update (Function.update (fun _ ↦ (0, fun _ ↦ 0, fun _ ↦ 0))
        ⟨0, by decide⟩ top) ⟨1, by decide⟩ middle) ⟨2, by decide⟩ bottom)⟩ =
      ⟨randomness, fun forsTree ↦ ofModelTreeOpening (opening forsTree),
        layerSignatures ⟨bottom.1, bottom.2.1, fun level ↦ bottom.2.2 level.val⟩
          ⟨middle.1, middle.2.1, fun level ↦ middle.2.2 level.val⟩
          ⟨top.1, top.2.1, fun level ↦ top.2.2 level.val⟩⟩ := by
  simp only [ofModelSignature]
  congr 1
  funext layer
  fin_cases layer <;> rfl

theorem forsKeyPayload_eq (key : FORS.ForsKey) :
    FORS.Concrete.rootsPayload key = Verification.forsKeyPayload key := rfl

/-- **The crate's signer, simulated, is the statement's**: the derivation of the scheme seed and
the parameter, then `sign_with`. -/
theorem simulateQ_sign (secretKey : MasterSeed) (message : FORS.Message) :
    Option.map ofModelSignature <$> simulateQ σ ((deriveSeeded secretKey >>= fun derived ↦
      FORS.Seeded.sign (m := OracleComp FORS.HashSpec) ⟨derived.1, derived.2, 0⟩ message :
        OracleComp FORS.HashSpec _)) =
      sign queryPermutation secretKey message := by
  rw [sim_bind, simulateQ_deriveSeeded]
  simp only [bind_assoc, pure_bind]
  unfold sign signWithSchemeSeed
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun schemeSeed ↦ ?_)
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun parameter ↦ ?_)
  rw [FORS.Seeded.sign, sim_bind, simulateQ_deriveRandomizer, bind_assoc]
  simp only [th, bind_assoc, pure_bind]
  erw [randomizerHashInput_eq]
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun output ↦ ?_)
  erw [sim_bind, simulateQ_messageDigest]
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun digest ↦ ?_)
  erw [sim_bind, ← simulateQ_forsOpenOnce, bind_map_left]
  refine (map_bind _ _ _).trans (bind_eq_of rfl fun fors ↦ ?_)
  rw [show FORS.numLayers = 3 from rfl]
  simp only [FORS.Seeded.signLayersUp, signLayer, sim_bind, bind_assoc]
  rw [show FORS.Seeded.layerFromBottom 0 = (⟨2, by decide⟩ : FORS.Layer) from rfl,
    show FORS.Seeded.layerFromBottom (0 + 1) = (⟨1, by decide⟩ : FORS.Layer) from rfl,
    show FORS.Seeded.layerFromBottom (0 + 1 + 1) = (⟨0, by decide⟩ : FORS.Layer) from rfl]
  refine (map_bind _ _ _).trans
    (bind_eq_of (simulateQ_layerOtsSign parameter schemeSeed _ ⟨2, by decide⟩ _) fun r0 ↦ ?_)
  rcases r0 with _ | ⟨counter0, values0⟩
  · rw [sim_pure, pure_bind]; simp [sim_pure]
  simp only [sim_bind, sim_pure, map_bind, bind_assoc, pure_bind]
  refine bind_eq_of (simulateQ_layerTree parameter schemeSeed _ ⟨2, by decide⟩) fun built0 ↦ ?_
  refine bind_eq_of (simulateQ_layerOtsSign parameter schemeSeed _ ⟨1, by decide⟩ _) fun r1 ↦ ?_
  rcases r1 with _ | ⟨counter1, values1⟩
  · simp [sim_pure]
  simp only [sim_bind, sim_pure, bind_assoc, pure_bind]
  refine bind_eq_of (simulateQ_layerTree parameter schemeSeed _ ⟨1, by decide⟩) fun built1 ↦ ?_
  refine bind_eq_of (simulateQ_layerOtsSign parameter schemeSeed _ ⟨0, by decide⟩ _) fun r2 ↦ ?_
  rcases r2 with _ | ⟨counter2, values2⟩
  · simp [sim_pure]
  simp only [sim_bind, sim_pure, bind_assoc, pure_bind]
  refine bind_eq_of (simulateQ_layerTree parameter schemeSeed _ ⟨0, by decide⟩) fun built2 ↦ ?_
  simp only [Option.map_some]
  rw [sim_pure, map_pure, Option.map_some, ofModelSignature_layersOfData]
  rfl

end Signing

end Sphincs.Model
