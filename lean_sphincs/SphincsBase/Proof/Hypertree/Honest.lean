import SphincsBase.Proof.Base.Prelude
import SphincsBase.Proof.Fts.ExtractFts
import SphincsBase.Proof.Ots.ExtractOts
import SphincsBase.Proof.Hypertree.Position
/-!
# The honest key at a position

One payload per position, one input, one value, all as functions of an answer function and the
sampled secrets. Nothing here is a recursion: each family reads the honest computation the statement
already defines, `honestChain`, `honestNode` and `honestFtsNode`, so the value at a position is
whatever those say. What the accounting needs of them is `honestPayload_congr`: the payload at a
position is a function of the values at its children, so two answer functions that agree on the
children agree on the input, which is what pins the honest structure to a cache.

`Valid` excludes the positions `Position` over-approximates, a node whose children would fall
outside the index width. They carry no honest meaning, and excluding them is what keeps
`honestPayload_congr` true of every position the accounting settles.
-/

namespace SphincsBase

open OracleComp

namespace Concrete

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)

/-- The value the honest forest's root hash carries. -/
def honestFtsKey (index : Index) (secret : FtsTree → FtsLeaf → Digest) : Digest :=
  evalWithAnswerFn f (ftsKey parameter index secret)

theorem honestFtsKey_eq (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    honestFtsKey f parameter index secret
      = truncateHash (f (tweakableHashInput parameter (.ftsRoots index)
          (ftsRootsPayload fun tree =>
            honestFtsNode f parameter index tree (secret tree) ftsTreeHeight 0))) := by
  simp only [honestFtsKey, ftsKey, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    eval_tweakableHash, honestFtsNode]

theorem honestChain_zero (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (secret : Digest) :
    honestChain f parameter lay tree leafIdx chainIdx secret 0 = secret := by
  simp [honestChain, chainWalk]

end Concrete

variable (f g : QueryImpl HashSpec Id) (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

/-- The payload the honest key hashes at a position. -/
noncomputable def honestPayload : Position → HashInput
  | .chain lay tree leafIdx chainIdx step =>
      Concrete.digestBytes (Concrete.honestChain f parameter lay tree leafIdx chainIdx
        (otsSecret lay tree leafIdx chainIdx) step.val)
  | .leaf lay tree leafIdx =>
      Concrete.leafPayload
        (Concrete.honestEndpoints f parameter lay tree (otsSecret lay tree) leafIdx)
  | .node lay tree level nodeIdx =>
      Concrete.nodePayload
        (Concrete.honestNode f parameter lay tree (otsSecret lay tree) level.val (2 * nodeIdx.val))
        (Concrete.honestNode f parameter lay tree (otsSecret lay tree) level.val
          (2 * nodeIdx.val + 1))
  | .ftsLeaf index tree leafIdx => Concrete.digestBytes (ftsSecret index tree leafIdx)
  | .ftsNode index tree level nodeIdx =>
      Concrete.nodePayload
        (Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) level.val
          (2 * nodeIdx.val))
        (Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) level.val
          (2 * nodeIdx.val + 1))
  | .ftsRoots index =>
      Concrete.ftsRootsPayload fun tree =>
        Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) ftsTreeHeight 0

/-- The input the honest key hashes at a position. -/
noncomputable def honestInput (p : Position) : HashInput :=
  tweakableHashInput parameter p.domain (honestPayload f parameter otsSecret ftsSecret p)

/-- The value the honest key carries at a position. -/
noncomputable def honestValue (p : Position) : Digest :=
  truncateHash (f (honestInput f parameter otsSecret ftsSecret p))

/-! ### What the value at a position is

The honest computations of the statement, read off the definitions above. -/

theorem honestValue_chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) :
    honestValue f parameter otsSecret ftsSecret (.chain lay tree leafIdx chainIdx step)
      = Concrete.honestChain f parameter lay tree leafIdx chainIdx
          (otsSecret lay tree leafIdx chainIdx) (step.val + 1) := by
  rw [Concrete.honestChain_succ f parameter lay tree leafIdx chainIdx _ step.val step.isLt]
  rfl

theorem honestValue_leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    honestValue f parameter otsSecret ftsSecret (.leaf lay tree leafIdx)
      = Concrete.honestNode f parameter lay tree (otsSecret lay tree) 0 leafIdx.val := by
  rw [Concrete.honestNode_zero_eq_leafHash f parameter lay tree (otsSecret lay tree) leafIdx]
  rfl

theorem honestValue_node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) :
    honestValue f parameter otsSecret ftsSecret (.node lay tree level nodeIdx)
      = Concrete.honestNode f parameter lay tree (otsSecret lay tree) (level.val + 1)
          nodeIdx.val := by
  rw [Concrete.honestNode_succ f parameter lay tree (otsSecret lay tree) level.val nodeIdx.val]
  rfl

theorem honestValue_ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) :
    honestValue f parameter otsSecret ftsSecret (.ftsLeaf index tree leafIdx)
      = Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) 0 leafIdx.val := by
  rw [Concrete.honestFtsNode_zero f parameter index tree (ftsSecret index tree) leafIdx]
  rfl

theorem honestValue_ftsNode (index : Index) (tree : FtsTree) (level : Fin ftsTreeHeight)
    (nodeIdx : FtsLeaf) :
    honestValue f parameter otsSecret ftsSecret (.ftsNode index tree level nodeIdx)
      = Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) (level.val + 1)
          nodeIdx.val := by
  rw [Concrete.honestFtsNode_succ f parameter index tree (ftsSecret index tree) level.val
    nodeIdx.val]
  rfl

/-! ### The payload is a concatenation of the values below

Every payload of the instance is the same shape: the values at the position's children, written as
`16` bytes each, one after another, or the secret the family starts from. Reading it that way once is
what makes the accounting generic: the payload is a function of the children's values, and it
determines each of them.
-/

/-- The positions `Position` over-approximates: a node whose children would fall outside the index
width. Nothing honest lives there, and the accounting never settles one. -/
def Position.Valid : Position → Prop
  | .node _ _ _ nodeIdx => 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight
  | .ftsNode _ _ _ nodeIdx => 2 * nodeIdx.val + 1 < 2 ^ ftsTreeHeight
  | _ => True

/-- The values at a position's children. -/
noncomputable def childValues (p : Position) : List Digest :=
  p.children.map (honestValue f parameter otsSecret ftsSecret)

/-- The values a position's payload concatenates: those at its children, or the secret its family
starts from. -/
noncomputable def slots : Position → List Digest
  | .chain lay tree leafIdx chainIdx step =>
      if step.val = 0 then [otsSecret lay tree leafIdx chainIdx]
      else childValues f parameter otsSecret ftsSecret (.chain lay tree leafIdx chainIdx step)
  | .ftsLeaf index tree leafIdx => [ftsSecret index tree leafIdx]
  | p => childValues f parameter otsSecret ftsSecret p

end SphincsBase
