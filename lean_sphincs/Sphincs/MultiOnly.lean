import Sphincs.MultiClass
import Sphincs.BridgeDetInternalize

/-! **The hash calls of one key.** Every hash input of the honest algorithms of the key with public
parameter `P`, except the two seed derivations of key generation (`leanSPHINCS || S0` and the
parameter derivation `0 || A(5) || S`), starts with the 16 bytes of `P` (`OnlyK P`): the tweakable
hashes, the seed derivations under `P`, the randomizer derivation and the message digest. -/

open OracleComp OracleSpec

namespace Sphincs.Security.KeyOnly

open Concrete Short

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

/-- Every hash query of the computation is an input of the key with parameter `p`. -/
def OnlyK (p : PublicParameter) {α : Type} (oa : OracleComp HashSpec α) : Prop :=
  oa.IsQueryBoundP (fun input => ¬OfKey p input) 0

theorem OnlyK.pure' {p : PublicParameter} {α : Type} (value : α) : OnlyK p (pure value : OracleComp HashSpec α) :=
  trivial

theorem OnlyK.bind {p : PublicParameter} {α β : Type} {oa : OracleComp HashSpec α}
    {next : α → OracleComp HashSpec β} (h : OnlyK p oa) (hnext : ∀ value, OnlyK p (next value)) :
    OnlyK p (oa >>= next) := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa [OnlyK] using this

theorem OnlyK.map {p : PublicParameter} {α β : Type} {oa : OracleComp HashSpec α} (f : α → β) (h : OnlyK p oa) :
    OnlyK p (f <$> oa) := by
  rw [OnlyK, isQueryBoundP_map_iff]
  exact h

theorem OnlyK.ite {p : PublicParameter} {α : Type} (condition : Prop) [Decidable condition]
    {left right : OracleComp HashSpec α} (hleft : OnlyK p left) (hright : OnlyK p right) :
    OnlyK p (if condition then left else right) := by
  split
  · exact hleft
  · exact hright

theorem OnlyK.query {p : PublicParameter} {input : HashInput} (h : OfKey p input) :
    OnlyK p (oracleHash input : OracleComp HashSpec HashOutput) := by
  simp only [OnlyK, oracleHash, HasQuery.query]
  rw [isQueryBoundP_query_iff]
  intro hnot
  exact absurd h hnot

theorem OnlyK.tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    OnlyK parameter (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) := by
  unfold Concrete.tweakableHash
  exact OnlyK.bind (OnlyK.query (ofKey_tweakable _ _ _)) (fun _ => OnlyK.pure' _)

theorem ofKey_keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    OfKey parameter (keygenHashInput parameter domain seed) :=
  ofKey_append _ _

theorem OnlyK.deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    OnlyK parameter (Sphincs.deriveKey parameter domain seed : OracleComp HashSpec Digest) := by
  unfold Sphincs.deriveKey
  exact OnlyK.bind (OnlyK.query (ofKey_keygenHashInput _ _ _)) (fun _ => OnlyK.pure' _)

theorem OnlyK.deriveOutput (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    OnlyK parameter (Sphincs.deriveOutput parameter domain seed : OracleComp HashSpec HashOutput) := by
  unfold Sphincs.deriveOutput
  exact OnlyK.query (ofKey_keygenHashInput _ _ _)

theorem OnlyK.deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed) (message : Message) :
    OnlyK parameter (Sphincs.deriveRandomizer parameter seed message : OracleComp HashSpec Randomness) := by
  unfold Sphincs.deriveRandomizer
  exact OnlyK.bind (OnlyK.query (ofKey_append _ _)) (fun _ => OnlyK.pure' _)

theorem OnlyK.sequenceFin {p : PublicParameter} {α : Type} {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (h : ∀ i, OnlyK p (computation i)) : OnlyK p (Concrete.sequenceFin computation) := by
  induction n with
  | zero => exact OnlyK.pure' _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      exact OnlyK.bind (h 0) (fun _ => OnlyK.bind (ih _ (fun i => h i.succ)) (fun _ => OnlyK.pure' _))

theorem OnlyK.chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start : Nat) :
    ∀ steps value, OnlyK parameter (Concrete.chainWalk parameter lay tree leaf chainIdx start steps value :
      OracleComp HashSpec Digest)
  | 0, value => OnlyK.pure' _
  | steps + 1, value => by
      rw [Concrete.chainWalk]
      refine OnlyK.bind (OnlyK.chainWalk parameter lay tree leaf chainIdx start steps value) ?_
      intro previous
      split
      · exact OnlyK.tweakableHash _ _ _
      · exact OnlyK.pure' _

theorem OnlyK.leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (endpoints : ChainIndex → Digest) :
    OnlyK parameter (Concrete.leafHash parameter lay tree leaf endpoints : OracleComp HashSpec Digest) :=
  OnlyK.tweakableHash _ _ _

theorem OnlyK.encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    OnlyK parameter (Concrete.encode parameter lay tree leaf message counter :
      OracleComp HashSpec (Option Encoding)) := by
  unfold Concrete.encode
  exact OnlyK.bind (OnlyK.tweakableHash _ _ _) (fun _ => OnlyK.pure' _)

theorem OnlyK.otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) (counter : Counter) (values : ChainIndex → Digest) :
    OnlyK parameter (Concrete.otsLeaf parameter lay tree leaf message counter values :
      OracleComp HashSpec (Option Digest)) := by
  unfold Concrete.otsLeaf
  refine OnlyK.bind (OnlyK.encode _ _ _ _ _ _) ?_
  intro encoding
  cases encoding with
  | none => exact OnlyK.pure' _
  | some encoding =>
      exact OnlyK.bind (OnlyK.sequenceFin _ fun chainIdx => OnlyK.chainWalk _ _ _ _ _ _ _ _)
        (fun _ => OnlyK.bind (OnlyK.leafHash _ _ _ _ _) (fun _ => OnlyK.pure' _))

theorem OnlyK.treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) :
    ∀ levels value, OnlyK parameter (Concrete.treeFold parameter lay tree leaf path levels value :
      OracleComp HashSpec Digest)
  | 0, value => OnlyK.pure' _
  | levels + 1, value => by
      rw [Concrete.treeFold]
      refine OnlyK.bind (OnlyK.treeFold parameter lay tree leaf path levels value) ?_
      intro current
      split <;> exact OnlyK.tweakableHash _ _ _

theorem OnlyK.forestWalk (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (i : FChain) (start : Nat) :
    ∀ steps value, OnlyK parameter (Concrete.forestWalk parameter index c s j a i start steps value :
      OracleComp HashSpec Digest)
  | 0, value => OnlyK.pure' _
  | steps + 1, value => by
      rw [Concrete.forestWalk]
      refine OnlyK.bind (OnlyK.forestWalk parameter index c s j a i start steps value) ?_
      intro previous
      split
      · exact OnlyK.tweakableHash _ _ _
      · exact OnlyK.pure' _

theorem OnlyK.childLeafHash (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (ends : FChain → Digest) :
    OnlyK parameter (Concrete.childLeafHash parameter index c s j a ends : OracleComp HashSpec Digest) :=
  OnlyK.tweakableHash _ _ _

theorem OnlyK.subFold (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (path : Fin subHeight → Digest) :
    ∀ levels value, OnlyK parameter (Concrete.subFold parameter index c s j a path levels value :
      OracleComp HashSpec Digest)
  | 0, value => OnlyK.pure' _
  | levels + 1, value => by
      rw [Concrete.subFold]
      refine OnlyK.bind (OnlyK.subFold parameter index c s j a path levels value) ?_
      intro current
      dsimp only
      split_ifs
      · exact OnlyK.tweakableHash _ _ _
      · exact OnlyK.tweakableHash _ _ _
      · exact OnlyK.pure' _

theorem OnlyK.topFold (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (path : Fin topHeight → Digest) :
    ∀ levels value, OnlyK parameter (Concrete.topFold parameter index c s path levels value :
      OracleComp HashSpec Digest)
  | 0, value => OnlyK.pure' _
  | levels + 1, value => by
      rw [Concrete.topFold]
      refine OnlyK.bind (OnlyK.topFold parameter index c s path levels value) ?_
      intro current
      dsimp only
      split_ifs
      · exact OnlyK.tweakableHash _ _ _
      · exact OnlyK.tweakableHash _ _ _
      · exact OnlyK.pure' _

theorem OnlyK.forestRecover (parameter : PublicParameter) (index : Index)
    (marks : Coord → CoordMark) (opening : Coord → CoordOpening) :
    OnlyK parameter (Concrete.forestRecover parameter index marks opening : OracleComp HashSpec Digest) := by
  unfold Concrete.forestRecover Concrete.coordRecover
  refine OnlyK.bind (OnlyK.sequenceFin _ fun c => ?_) ?_
  · refine OnlyK.bind (OnlyK.sequenceFin _ fun j => ?_) (fun tops => ?_)
    · unfold Concrete.childRecover Concrete.forestRecoverChain
      exact OnlyK.bind (OnlyK.bind (OnlyK.sequenceFin _ fun _ => OnlyK.forestWalk _ _ _ _ _ _ _ _ _ _)
        (fun _ => OnlyK.childLeafHash _ _ _ _ _ _ _))
        (fun _ => OnlyK.bind (OnlyK.subFold _ _ _ _ _ _ _ _ _) (fun _ => OnlyK.pure' _))
    · unfold Concrete.superHash
      exact OnlyK.bind (OnlyK.tweakableHash _ _ _)
        (fun _ => OnlyK.bind (OnlyK.topFold _ _ _ _ _ _ _) (fun _ => OnlyK.pure' _))
  · intro tops
    exact OnlyK.tweakableHash _ _ _

theorem OnlyK.messageDigestCall (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    OnlyK parameter (Concrete.messageDigestCall parameter root message randomness :
      OracleComp HashSpec HashOutput) := by
  unfold Concrete.messageDigestCall
  exact OnlyK.query (ofKey_tweakable _ _ _)

theorem OnlyK.messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    OnlyK parameter (Concrete.messageDigest parameter root message randomness :
      OracleComp HashSpec MessageDigest) := by
  unfold Concrete.messageDigest
  exact OnlyK.bind (OnlyK.messageDigestCall _ _ _ _) (fun _ => OnlyK.pure' _)

attribute [local irreducible] Concrete.treeFold Concrete.chainWalk
  Concrete.otsLeaf Concrete.forestRecover Concrete.messageDigest

theorem OnlyK.verify (publicKey : PublicKey) (message : Message) (signature : Signature) :
    OnlyK publicKey.parameter (Concrete.verify publicKey message signature : OracleComp HashSpec Bool) := by
  rw [verify_eq_single_layer]
  refine OnlyK.bind (OnlyK.messageDigest _ _ _ _) ?_
  intro digest
  refine OnlyK.bind (OnlyK.forestRecover _ _ _ _) ?_
  intro key
  refine OnlyK.bind (OnlyK.otsLeaf _ _ _ _ _ _ _) ?_
  intro value
  cases value with
  | none => exact OnlyK.pure' _
  | some value =>
      exact OnlyK.bind (OnlyK.treeFold publicKey.parameter topLayer rootTree _ _ totalHeight value)
        (fun _ => OnlyK.pure' _)

namespace Seeded
open Sphincs.Seeded

theorem OnlyK.otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    OnlyK parameter (otsSecrets parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) :=
  OnlyK.bind (OnlyK.sequenceFin _ fun _ => OnlyK.deriveOutput _ _ _)
    (fun _ => OnlyK.pure' _)

theorem OnlyK.oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    OnlyK parameter (oneTimePublicKey parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) :=
  OnlyK.bind (OnlyK.otsSecrets _ _ _ _ _) (fun _ =>
    OnlyK.sequenceFin _ fun _ => OnlyK.chainWalk _ _ _ _ _ _ _ _)

theorem OnlyK.otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : Digest) :
    ∀ attempts counter, OnlyK parameter (otsSignFrom parameter lay tree leaf seed message attempts counter :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))
  | 0, _ => OnlyK.pure' _
  | attempts + 1, counter => by
      rw [Sphincs.Seeded.otsSignFrom]
      refine OnlyK.bind (OnlyK.encode _ _ _ _ _ _) ?_
      intro encoding
      cases encoding with
      | none => exact OnlyK.otsSignFrom parameter lay tree leaf seed message attempts (counter + 1)
      | some encoding =>
          exact OnlyK.bind (OnlyK.otsSecrets _ _ _ _ _) (fun _ =>
            OnlyK.bind (OnlyK.sequenceFin _ fun _ => OnlyK.chainWalk _ _ _ _ _ _ _ _)
              (fun _ => OnlyK.pure' _))

theorem OnlyK.treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : ∀ level nodeIdx, OnlyK parameter (treeNode parameter lay tree seed level nodeIdx :
      OracleComp HashSpec Digest)
  | 0, nodeIdx => by
      rw [Sphincs.Seeded.treeNode]
      exact OnlyK.bind (OnlyK.oneTimePublicKey _ _ _ _ _) (fun _ => OnlyK.leafHash _ _ _ _ _)
  | level + 1, nodeIdx => by
      rw [Sphincs.Seeded.treeNode]
      exact OnlyK.bind (OnlyK.treeNode parameter lay tree seed level _) (fun _ =>
        OnlyK.bind (OnlyK.treeNode parameter lay tree seed level _) (fun _ =>
          OnlyK.tweakableHash _ _ _))

theorem OnlyK.chainValue (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (i : FChain) (seed : MasterSeed) (pos : Nat) :
    OnlyK parameter (chainValue parameter index c s j a i seed pos : OracleComp HashSpec Digest) :=
  OnlyK.bind (OnlyK.bind (OnlyK.deriveOutput _ _ _) (fun _ => OnlyK.pure' _))
    (fun _ => OnlyK.forestWalk _ _ _ _ _ _ _ _ _ _)

theorem OnlyK.forestSecrets (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (seed : MasterSeed) :
    OnlyK parameter (forestSecrets parameter index c s j a seed : OracleComp HashSpec (FChain → Digest)) :=
  OnlyK.bind (OnlyK.sequenceFin _ fun _ => OnlyK.deriveOutput _ _ _)
    (fun _ => OnlyK.pure' _)

theorem OnlyK.subNode (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (seed : MasterSeed) : ∀ level node, OnlyK parameter (subNode parameter index c s j seed level node :
      OracleComp HashSpec Digest)
  | 0, node => by
      rw [Sphincs.Seeded.subNode]
      exact OnlyK.bind (OnlyK.forestSecrets _ _ _ _ _ _ _) (fun _ =>
        OnlyK.bind (OnlyK.sequenceFin _ fun _ => OnlyK.forestWalk _ _ _ _ _ _ _ _ _ _)
          (fun _ => OnlyK.childLeafHash _ _ _ _ _ _ _))
  | level + 1, node => by
      rw [Sphincs.Seeded.subNode]
      refine OnlyK.bind (OnlyK.subNode parameter index c s j seed level _) (fun _ =>
        OnlyK.bind (OnlyK.subNode parameter index c s j seed level _) (fun _ => ?_))
      split
      · exact OnlyK.tweakableHash _ _ _
      · exact OnlyK.pure' _

theorem OnlyK.superNode (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (seed : MasterSeed) : OnlyK parameter (superNode parameter index c s seed : OracleComp HashSpec Digest) := by
  unfold Sphincs.Seeded.superNode Concrete.superHash
  exact OnlyK.bind (OnlyK.sequenceFin _ fun _ =>
      OnlyK.bind (OnlyK.subNode _ _ _ _ _ _ _ _) (fun _ =>
        OnlyK.bind (OnlyK.subNode _ _ _ _ _ _ _ _) (fun _ => OnlyK.pure' _)))
    (fun _ => OnlyK.tweakableHash _ _ _)

theorem OnlyK.topNode (parameter : PublicParameter) (index : Index) (c : Coord)
    (seed : MasterSeed) : ∀ level node, OnlyK parameter (topNode parameter index c seed level node :
      OracleComp HashSpec Digest)
  | 0, node => by
      rw [Sphincs.Seeded.topNode]
      exact OnlyK.superNode _ _ _ _ _
  | level + 1, node => by
      rw [Sphincs.Seeded.topNode]
      refine OnlyK.bind (OnlyK.topNode parameter index c seed level _) (fun _ =>
        OnlyK.bind (OnlyK.topNode parameter index c seed level _) (fun _ => ?_))
      split
      · exact OnlyK.tweakableHash _ _ _
      · exact OnlyK.pure' _

theorem OnlyK.forestKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) :
    OnlyK parameter (forestKey parameter index seed : OracleComp HashSpec Digest) := by
  have htop : ∀ c, OnlyK parameter (do
      let left ← Sphincs.Seeded.topNode parameter index c seed (topHeight - 1) 0
      let right ← Sphincs.Seeded.topNode parameter index c seed (topHeight - 1) 1
      return (left, right) : OracleComp HashSpec (Digest × Digest)) :=
    fun c => OnlyK.bind (OnlyK.topNode parameter index c seed _ _) (fun _ =>
      OnlyK.bind (OnlyK.topNode parameter index c seed _ _) (fun _ => OnlyK.pure' _))
  have hroots : ∀ tops : Coord → Digest × Digest,
      OnlyK parameter (Concrete.tweakableHash parameter (.roots index) (rootsPayload tops) :
        OracleComp HashSpec Digest) := fun tops =>
    OnlyK.tweakableHash _ _ _
  unfold Sphincs.Seeded.forestKey
  exact OnlyK.bind (OnlyK.sequenceFin _ htop) hroots

theorem OnlyK.forestOpen (parameter : PublicParameter) (index : Index) (marks : Coord → CoordMark)
    (seed : MasterSeed) :
    OnlyK parameter (forestOpen parameter index marks seed : OracleComp HashSpec (Coord → CoordOpening)) := by
  unfold Sphincs.Seeded.forestOpen Sphincs.Seeded.coordOpen
  exact OnlyK.sequenceFin _ fun _ =>
    OnlyK.bind (OnlyK.sequenceFin _ fun _ =>
      OnlyK.bind (OnlyK.forestSecrets _ _ _ _ _ _ _) (fun _ =>
        OnlyK.bind (OnlyK.sequenceFin _ fun _ => OnlyK.forestWalk _ _ _ _ _ _ _ _ _ _) (fun _ =>
          OnlyK.bind (OnlyK.sequenceFin _ fun _ => OnlyK.subNode _ _ _ _ _ _ _ _)
            (fun _ => OnlyK.pure' _)))) (fun _ =>
      OnlyK.bind (OnlyK.sequenceFin _ fun _ => OnlyK.topNode _ _ _ _ _ _)
        (fun _ => OnlyK.pure' _))

variable [Params]

omit [Params] in
theorem OnlyK.surrogate (parameter : PublicParameter) (seed : MasterSeed) (level : Nat) :
    OnlyK parameter (surrogate parameter seed level : OracleComp HashSpec Digest) := by
  unfold Sphincs.Seeded.surrogate
  split
  · exact OnlyK.deriveKey _ _ _
  · exact OnlyK.pure' _

theorem OnlyK.spineNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : ∀ steps, OnlyK parameter (spineNode parameter lay tree seed steps :
      OracleComp HashSpec Digest)
  | 0 => by
      rw [Sphincs.Seeded.spineNode]
      exact OnlyK.treeNode _ _ _ _ _ _
  | steps + 1 => by
      rw [Sphincs.Seeded.spineNode]
      refine OnlyK.bind (OnlyK.spineNode parameter lay tree seed steps) (fun _ =>
        OnlyK.bind (OnlyK.surrogate _ _ _) (fun _ => ?_))
      dsimp only
      exact OnlyK.ite _ (OnlyK.tweakableHash _ _ _)
        (OnlyK.tweakableHash _ _ _)

theorem OnlyK.treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : OnlyK parameter (treeRoot parameter lay tree seed : OracleComp HashSpec Digest) :=
  OnlyK.spineNode _ _ _ _ _

theorem OnlyK.treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) :
    OnlyK parameter (treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest)) :=
  OnlyK.sequenceFin _ fun level => by
    split
    · exact OnlyK.treeNode _ _ _ _ _ _
    · exact OnlyK.surrogate _ _ _

theorem OnlyK.signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    OnlyK secretKey.parameter (signAttempt secretKey message randomness : OracleComp HashSpec (Option Index)) := by
  unfold Sphincs.Seeded.signAttempt
  exact OnlyK.bind (OnlyK.messageDigestCall _ _ _ _) (fun _ =>
    OnlyK.ite _ (OnlyK.pure' _) (OnlyK.pure' _))

attribute [local irreducible] Sphincs.Seeded.treeNode Sphincs.Seeded.subNode
  Sphincs.Seeded.topNode Sphincs.Seeded.otsSignFrom Sphincs.Seeded.forestKey
  Sphincs.Seeded.treePath

theorem OnlyK.signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    OnlyK secretKey.parameter (signLayer secretKey index lay : OracleComp HashSpec (Option (LayerSignature lay))) := by
  unfold Sphincs.Seeded.signLayer Sphincs.Seeded.layerMessage Sphincs.Seeded.otsSign
  dsimp only
  generalize treeIndexAt index lay = tree
  generalize leafIndexAt index lay = leaf
  refine OnlyK.bind (OnlyK.forestKey _ _ _) (fun _ => ?_)
  refine OnlyK.bind (OnlyK.otsSignFrom _ _ _ _ _ _ _ _) (fun result => ?_)
  rcases result with _ | ⟨counter, values⟩
  · exact OnlyK.pure' _
  · exact OnlyK.bind (OnlyK.treePath _ _ _ _ _) (fun _ => OnlyK.pure' _)

end Seeded

variable [Params]

attribute [local irreducible] Sphincs.Seeded.signLayer Sphincs.Seeded.forestOpen

theorem OnlyK.finishSign (secretKey : Sphincs.Seeded.SecretKey) (message : Message)
    (randomness : Randomness) :
    OnlyK secretKey.parameter (Randomized.finishSign secretKey message randomness :
      OracleComp HashSpec (Option Signature)) := by
  unfold Randomized.finishSign
  refine OnlyK.bind (OnlyK.messageDigest _ _ _ _) (fun digest => ?_)
  dsimp only
  generalize digestIndex digest = index
  generalize digestMarks digest = marks
  refine OnlyK.bind (Seeded.OnlyK.forestOpen _ _ _ _) (fun _ => ?_)
  unfold sequenceLayers
  refine OnlyK.bind ?_ (fun layers => ?_)
  · exact OnlyK.bind (Seeded.OnlyK.signLayer secretKey index topLayer) (fun top => by
      rcases top with _ | top <;> exact OnlyK.pure' _)
  · rcases layers with _ | layers <;> exact OnlyK.pure' _


namespace Seeded

attribute [local irreducible] Randomized.finishSign Sphincs.Seeded.signAttempt

theorem OnlyK.seededLoop (sk : Sphincs.Seeded.SecretKey) (message : Message) :
    ∀ attempts randomness, OnlyK sk.parameter (Sphincs.Seeded.signDigestLoop sk message attempts randomness :
      OracleComp HashSpec (Option (Randomness × Index)))
  | 0, _ => OnlyK.pure' _
  | attempts + 1, randomness => by
      rw [Sphincs.Seeded.signDigestLoop]
      refine OnlyK.bind (OnlyK.signAttempt _ _ _) (fun result => ?_)
      cases result with
      | none => exact OnlyK.seededLoop sk message attempts (randomness + 1)
      | some _ => exact OnlyK.pure' _

/-- **The deterministic signer only queries inputs of its key.** -/
theorem OnlyK.seededSign (sk : Sphincs.Seeded.SecretKey) (message : Message) :
    OnlyK sk.parameter (Sphincs.Seeded.sign sk message : OracleComp HashSpec (Option Signature)) := by
  rw [Det.seededSign_eq]
  refine OnlyK.bind (OnlyK.deriveRandomizer _ _ _) (fun base => ?_)
  refine OnlyK.bind (OnlyK.seededLoop sk message _ _) (fun result => ?_)
  rcases result with _ | ⟨randomness, _⟩
  · exact OnlyK.pure' _
  · exact KeyOnly.OnlyK.finishSign _ _ _

/-- Key generation from the scheme seed: the parameter derivation, then inputs of the derived key. -/
theorem keygenFromMaster_eq (seed : MasterSeed) :
    (Sphincs.Seeded.keygenFromMaster seed : OracleComp HashSpec (PublicKey × Sphincs.Seeded.SecretKey)) =
      Sphincs.deriveKey 0 .parameter seed >>= fun parameter =>
        Sphincs.Seeded.treeRoot parameter topLayer rootTree seed >>= fun root =>
          pure (⟨root, parameter⟩, ⟨seed, parameter, root⟩) := rfl

theorem OnlyK.keyRoot (parameter : PublicParameter) (seed : MasterSeed) :
    OnlyK parameter (Sphincs.Seeded.treeRoot parameter topLayer rootTree seed >>= fun root =>
      (pure (⟨root, parameter⟩, ⟨seed, parameter, root⟩) :
        OracleComp HashSpec (PublicKey × Sphincs.Seeded.SecretKey))) :=
  OnlyK.bind (OnlyK.treeRoot _ _ _ _) fun _ => OnlyK.pure' _

end Seeded

end Sphincs.Security.KeyOnly
