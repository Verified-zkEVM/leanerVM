import SphincsBase.Proof.Base.Prelude
import SphincsBase.Proof.IdealStatement

/-!
# Facts about the statement

`Scheme.lean` seals the two tree recursions against accidental unfolding, which also stops Lean from generating their equational theorems. Unsealing them locally makes the equations hold by `rfl`, so this module states them once as ordinary theorems and the rest of the development rewrites with those instead of unfolding anything. It also checks the arithmetic the concrete parameters fix: the layer heights, the index decomposition and the authentication path offsets.
-/

namespace SphincsBase.Concrete

attribute [local semireducible] treeNode ftsNode verify sign sampleRandomness

noncomputable local instance instSampleableTypeRandomness_1 : SampleableType Randomness :=
  randomnessSampleableType

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

@[simp]
theorem treeNode_zero_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (nodeIdx : Nat) :
    treeNode (m := m) parameter lay tree secret 0 nodeIdx
      = (do
          let endpoints ← oneTimePublicKey parameter lay tree (leafOfNat nodeIdx)
            (secret (leafOfNat nodeIdx))
          leafHash parameter lay tree (leafOfNat nodeIdx) endpoints) := rfl

theorem treeNode_succ_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    treeNode (m := m) parameter lay tree secret (level + 1) nodeIdx
      = (do
          let left ← treeNode parameter lay tree secret level (2 * nodeIdx)
          let right ← treeNode parameter lay tree secret level (2 * nodeIdx + 1)
          tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)) := rfl

@[simp]
theorem ftsNode_zero_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (nodeIdx : Nat) :
    ftsNode (m := m) parameter index tree secret 0 nodeIdx
      = ftsLeafHash parameter index tree (ftsLeafOfNat nodeIdx) (secret (ftsLeafOfNat nodeIdx)) := rfl

theorem ftsNode_succ_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    ftsNode (m := m) parameter index tree secret (level + 1) nodeIdx
      = (do
          let left ← ftsNode parameter index tree secret level (2 * nodeIdx)
          let right ← ftsNode parameter index tree secret level (2 * nodeIdx + 1)
          tweakableHash parameter (.ftsNode index tree (level + 1) nodeIdx)
            (nodePayload left right)) := rfl

theorem treeFold_succ_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) (levels : Nat) (value : Digest) :
    treeFold (m := m) parameter lay tree leaf path (levels + 1) value
      = (do
          let current ← treeFold parameter lay tree leaf path levels value
          if leaf.val.testBit levels then
            tweakableHash parameter (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload (path levels) current)
          else
            tweakableHash parameter (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload current (path levels))) := rfl

theorem ftsFold_succ_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest) (levels : Nat) (value : Digest) :
    ftsFold (m := m) parameter index tree leaf path (levels + 1) value
      = (do
          let current ← ftsFold parameter index tree leaf path levels value
          let sibling := if hlevel : levels < ftsTreeHeight then path ⟨levels, hlevel⟩ else 0
          if leaf.val.testBit levels then
            tweakableHash parameter (.ftsNode index tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload sibling current)
          else
            tweakableHash parameter (.ftsNode index tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload current sibling)) := rfl

attribute [local irreducible] verifyLayers

theorem verify_eq (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verify (m := m) publicKey message signature
      = (do
          let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
          if ¬ Admissible digest then
            return false
          else
            let ftsPublicKey ← ftsRecover publicKey.parameter (digestIndex digest)
              (digestLeaves digest) signature.ftsSecret signature.ftsPath
            match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
                ftsPublicKey with
            | none => return false
            | some root => return decide (root = publicKey.root)) := by
  unfold verify
  apply bind_congr
  intro digest
  split
  · rfl
  · apply bind_congr
    intro key
    apply bind_congr
    intro result
    cases result <;> rfl

theorem sign_eq (secretKey : SecretKey) (message : Message) :
    sign secretKey message
      = (do
          match ← signDigestLoop digestAttemptLimit secretKey message with
          | none => return none
          | some (randomness, index, leaves) => do
              let ftsPath ← liftM
                (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index) :
                  OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest))
              let layers ← liftM
                (sequenceLayers (fun lay => signLayer secretKey index lay) :
                  OracleComp HashSpec
                    (Option (Layer → Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))))
              match layers with
              | none => return none
              | some parts => do
                  let _ ← liftM
                    (treeRoot secretKey.parameter topLayer rootTree (secretKey.otsSecret topLayer rootTree) :
                      OracleComp HashSpec Digest)
                  return some
                    { randomness := randomness
                      ftsSecret := fun tree =>
                        secretKey.ftsSecret index tree (leaves (ftsIndexOf tree))
                      ftsPath := ftsPath
                      layers := fun lay => LayerSignature.ofPadded lay (parts lay) }) := rfl

example : ∀ failure : Fin 4,
    let result := (sequenceLayers (m := WriterT (List Nat) Id) fun lay =>
      WriterT.mk (pure (if lay.val = failure.val then none else some lay.val, [lay.val]))).run
    (result.2, result.1.map List.ofFn) =
      ![([2, 1, 0], none), ([2, 1], none), ([2], none), ([2, 1, 0], some [0, 1, 2])] failure := by
  decide

/-! ## Parameter arithmetic -/

example : ∑ lay : Layer, layerHeight lay = totalHeight := by decide

example : (layerHeight topLayer, layerHeight middleLayer, layerHeight bottomLayer) = (12, 7, 7) := by
  decide

example : (heightAbove topLayer, heightAbove middleLayer, heightAbove bottomLayer) = (0, 12, 19) := by
  decide

example : (heightBelow topLayer, heightBelow middleLayer, heightBelow bottomLayer) = (14, 7, 0) := by
  decide

/-- The digest is `h + k * a = 176` bits and has to fit in one oracle output. -/
example : messageDigestBits = 176 ∧ messageDigestBits ≤ hashOutputBits := by decide

end SphincsBase.Concrete
