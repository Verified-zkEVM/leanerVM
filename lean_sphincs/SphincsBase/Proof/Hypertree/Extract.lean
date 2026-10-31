import SphincsBase.Proof.Base.Prelude
import SphincsBase.Proof.Scheme.Arith
import SphincsBase.Proof.Scheme.Bytes
import SphincsBase.Proof.Scheme.StatementLemmas
/-!
# Extracting the first divergence

The deterministic half of the reduction, for one layer's tree. If a fold on values an adversary
supplies reaches the honest node above the leaf, then either every value it supplied was the honest
one, or at some level it hashed something other than the honest payload to the honest value. The
second is what the union bound charges; the first is what makes the adversary's signature the honest
one, and so no forgery.
-/

namespace SphincsBase.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (path : Nat → Digest)

/-- The value the honest tree carries at a position. -/
def honestNode (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (treeNode parameter lay tree secret level nodeIdx)

/-- What the fold has reached after `levels` steps. -/
def foldValue (value : Digest) (levels : Nat) : Digest :=
  evalWithAnswerFn f (treeFold parameter lay tree leaf path levels value)

/-- Two children in the order the bit dictates. Written with `Bool.rec` rather than `if`, so that
both cases hold by `rfl` and rewriting the bit needs no reasoning about `Decidable` instances. -/
def orderedPayload (bit : Bool) (current sibling : Digest) : HashInput :=
  bit.rec (nodePayload current sibling) (nodePayload sibling current)

/-- The payload the fold hashes on its way from `level` to `level + 1`. -/
def foldPayload (value : Digest) (level : Nat) : HashInput :=
  orderedPayload (leaf.val.testBit level)
    (foldValue f parameter lay tree leaf path value level) (path level)

theorem eval_tweakableHash (domain : HashDomain) (payload : HashInput) :
    evalWithAnswerFn f (tweakableHash parameter domain payload)
      = truncateHash (f (tweakableHashInput parameter domain payload)) := by
  simp only [tweakableHash, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_query,
    evalWithAnswerFn_pure]

theorem honestNode_succ (level nodeIdx : Nat) :
    honestNode f parameter lay tree secret (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
          (nodePayload (honestNode f parameter lay tree secret level (2 * nodeIdx))
            (honestNode f parameter lay tree secret level (2 * nodeIdx + 1))))) := by
  simp only [honestNode, treeNode_succ_eq, evalWithAnswerFn_bind, eval_tweakableHash]

theorem foldValue_succ (value : Digest) (level : Nat) :
    foldValue f parameter lay tree leaf path value (level + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.node lay tree (level + 1) (leaf.val / 2 ^ (level + 1)))
          (foldPayload f parameter lay tree leaf path value level))) := by
  simp only [foldValue, foldPayload, treeFold_succ_eq, evalWithAnswerFn_bind, orderedPayload]
  cases leaf.val.testBit level <;> rfl

/-- A hit at a node position: something other than the honest payload hashing to the honest value
there. Domain separation makes the target a function of the position alone, which is what lets the
union bound charge it. -/
def NodeHit (level nodeIdx : Nat) (payload : HashInput) : Prop :=
  payload ≠ nodePayload (honestNode f parameter lay tree secret level (2 * nodeIdx))
      (honestNode f parameter lay tree secret level (2 * nodeIdx + 1))
    ∧ truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx) payload))
      = honestNode f parameter lay tree secret (level + 1) nodeIdx

end SphincsBase.Concrete
