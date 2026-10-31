import SphincsBase.Proof.Base.Prelude
import SphincsBase.Proof.Scheme.Bytes
import SphincsBase.Proof.Ots.ExtractChain
import SphincsBase.Proof.Ots.OneTime
/-!
# Extracting a one-time signature

If the verifier's half of a one-time signature returns the honest leaf, then either the chain values
the adversary supplied are the honest ones at its codeword's positions, or it hit the leaf value, or
it hit a chain value. The first alternative is what the incomparability of the code turns into "the
signature is the one the signer produced".
-/

namespace SphincsBase.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex)

theorem leafOfNat_val : leafOfNat leaf.val = leaf := by
  ext
  simp [leafOfNat, Nat.mod_eq_of_lt leaf.isLt]

/-- The honest one-time public values at a leaf. -/
def honestEndpoints (chainIdx : ChainIndex) : Digest :=
  honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx) (chainLength - 1)

theorem honestEndpoints_def : honestEndpoints f parameter lay tree secret leaf
    = fun chainIdx => evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret leaf chainIdx)) :=
  rfl

/-- A hit at a leaf: something other than the honest endpoints hashing to the honest leaf. -/
def LeafHit (payload : HashInput) : Prop :=
  payload ≠ leafPayload (honestEndpoints f parameter lay tree secret leaf)
    ∧ truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf) payload))
      = honestNode f parameter lay tree secret 0 leaf.val

theorem honestNode_zero_eq_leafHash :
    honestNode f parameter lay tree secret 0 leaf.val
      = truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf)
          (leafPayload (honestEndpoints f parameter lay tree secret leaf)))) := by
  simp only [honestNode, treeNode_zero_eq, leafOfNat_val, evalWithAnswerFn_bind, leafHash,
    eval_tweakableHash, eval_oneTimePublicKey, honestEndpoints_def]

end SphincsBase.Concrete
