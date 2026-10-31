import SphincsBase.Proof.Base.Prelude
import SphincsBase.Proof.Ots.Chain
import SphincsBase.Proof.Scheme.Eval
/-!
# The one-time signature

`Ots.leaf` recovers the leaf `Ots.sign` committed to. The counter matters only through the codeword
it produces: correctness holds for *any* admissible counter, not just the least one the signer
takes, which is why a second admissible counter for the same codeword is a strong forgery rather
than a break.
-/

namespace SphincsBase.Concrete

open OracleComp

variable {α : Type} (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
  (tree : TreeIndex) (leaf : LeafIndex)

/-- Steps compose under evaluation. -/
theorem eval_chainWalk_add (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start (a + b) value)
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + a) b
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start a value))) := by
  rw [chainWalk_add, evalWithAnswerFn_bind]

/-- The honest one-time public value of one chain. -/
theorem eval_oneTimePublicKey (secret : ChainIndex → Digest) :
    evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf secret)
      = fun chainIdx => evalWithAnswerFn f
          (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx)) := by
  simp [oneTimePublicKey]

end SphincsBase.Concrete
