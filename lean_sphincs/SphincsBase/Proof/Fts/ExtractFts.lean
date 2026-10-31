import SphincsBase.Proof.Base.Prelude
import SphincsBase.Proof.Hypertree.Extract
/-!
# Extracting a few-time opening

The tree argument again, on one tree of the few-time forest, and then on the leaf below it. If a fold
on values an adversary supplied reaches the honest root, either it supplied the honest secret and the
honest siblings, or it hit a node, or it hit the leaf. Supplying the honest secret is the only
alternative that is not a hash break, and it means the secret was revealed by a signature: that is
the leak the parameters are chosen against.
-/

namespace SphincsBase.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (tree : FtsTree)
  (secret : FtsLeaf → Digest) (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest)

theorem ftsLeafOfNat_val : ftsLeafOfNat leaf.val = leaf := by
  ext
  simp [ftsLeafOfNat, Nat.mod_eq_of_lt leaf.isLt]

/-- The value the honest few-time tree carries at a position. -/
def honestFtsNode (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (ftsNode parameter index tree secret level nodeIdx)

/-- What the fold has reached after `levels` steps. -/
def ftsFoldValue (value : Digest) (levels : Nat) : Digest :=
  evalWithAnswerFn f (ftsFold parameter index tree leaf path levels value)

/-- The sibling the fold reads at a level, `0` past the tree's height. -/
def ftsSibling (level : Nat) : Digest :=
  if hlevel : level < ftsTreeHeight then path ⟨level, hlevel⟩ else 0

/-- The payload the fold hashes on its way from `level` to `level + 1`. -/
def ftsFoldPayload (value : Digest) (level : Nat) : HashInput :=
  orderedPayload (leaf.val.testBit level)
    (ftsFoldValue f parameter index tree leaf path value level) (ftsSibling path level)

theorem honestFtsNode_succ (level nodeIdx : Nat) :
    honestFtsNode f parameter index tree secret (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter (.ftsNode index tree (level + 1) nodeIdx)
          (nodePayload (honestFtsNode f parameter index tree secret level (2 * nodeIdx))
            (honestFtsNode f parameter index tree secret level (2 * nodeIdx + 1))))) := by
  simp only [honestFtsNode, ftsNode_succ_eq, evalWithAnswerFn_bind, eval_tweakableHash]

theorem honestFtsNode_zero (leafIdx : FtsLeaf) :
    honestFtsNode f parameter index tree secret 0 leafIdx.val
      = truncateHash (f (tweakableHashInput parameter (.ftsLeaf index tree leafIdx)
          (digestBytes (secret leafIdx)))) := by
  simp only [honestFtsNode, ftsNode_zero_eq, ftsLeafOfNat_val, ftsLeafHash, eval_tweakableHash]

theorem ftsFoldValue_succ (value : Digest) (level : Nat) :
    ftsFoldValue f parameter index tree leaf path value (level + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.ftsNode index tree (level + 1) (leaf.val / 2 ^ (level + 1)))
          (ftsFoldPayload f parameter index tree leaf path value level))) := by
  simp only [ftsFoldValue, ftsFoldPayload, ftsSibling, ftsFold_succ_eq, evalWithAnswerFn_bind,
    orderedPayload]
  cases leaf.val.testBit level <;> rfl

/-- A hit at a few-time node. -/
def FtsNodeHit (level nodeIdx : Nat) (payload : HashInput) : Prop :=
  payload ≠ nodePayload (honestFtsNode f parameter index tree secret level (2 * nodeIdx))
      (honestFtsNode f parameter index tree secret level (2 * nodeIdx + 1))
    ∧ truncateHash (f (tweakableHashInput parameter (.ftsNode index tree (level + 1) nodeIdx)
        payload)) = honestFtsNode f parameter index tree secret (level + 1) nodeIdx

/-- A hit at a few-time leaf: something other than the honest secret hashing to the honest leaf. -/
def FtsLeafHit (leafIdx : FtsLeaf) (candidate : Digest) : Prop :=
  candidate ≠ secret leafIdx
    ∧ truncateHash (f (tweakableHashInput parameter (.ftsLeaf index tree leafIdx)
        (digestBytes candidate))) = honestFtsNode f parameter index tree secret 0 leafIdx.val

end SphincsBase.Concrete
