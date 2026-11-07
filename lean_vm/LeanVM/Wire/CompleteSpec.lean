/-
  LeanVM.Wire.CompleteSpec

  The shared vocabulary of completeness on the wire: the hash inputs a Merkle path climbs through
  (`climbInput`, `ClimbInputsIn`) and a hash that records its inputs (`loggedHash`, `loggedPerm`).
-/

module

public import LeanVM.Wire.Spec

/-!
# Completeness on the wire: the hash inputs of an honest proof

Completeness on the wire (`LeanVM.Wire.Complete`) decodes the honest prover's bytes in the
random-permutation model, after the prover's run. Decoding re-hashes Merkle nodes (the leaves, and
each parent of a node and its sibling); in the lazily sampled permutation these calls answer as the
prover's did, and leave the permutation as it was, because the prover made them all when it built
its trees. This file names what that needs:

* `climbInput h path level`: the bytes hashed to reach `climbTo h path level`: the leaf's bytes at
  level `0`, then the node and its sibling, the position's bit choosing the side
  (`climbTo_eq_climbInput`);
* `ClimbInputsIn h proof log`: every input every path of `proof` climbs through, up to and
  including its root's, is in `log`;
* `loggedHash h`, `loggedPerm F`: the hash `h` and the permutation `F` in the state monad of the
  hash inputs so far, each hash input appended. The honest prover run with them
  (`Prover.proveWithHash (loggedHash h) (loggedPerm F)`) logs every byte string it hashes.
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-- The bytes hashed to reach `climbTo h path level`: the leaf's bytes at level `0`, then the node
the path climbed to and its sibling, the position's bit choosing the side. -/
def climbInput (h : Bytes → Digest) (path : Opening) : ℕ → Bytes
  | 0 => path.leaf.flatMap K.toBytes
  | level + 1 =>
    let node := climbTo h path level
    let sibling := path.path.getD level default
    if (path.leafIndex >>> level) % 2 = 0 then digestBytes node ++ digestBytes sibling
    else digestBytes sibling ++ digestBytes node

theorem climbTo_eq_climbInput (h : Bytes → Digest) (path : Opening) (level : ℕ) :
    climbTo h path level = h (climbInput h path level) := by
  cases level with
  | zero => rfl
  | succ level =>
    simp only [climbTo, climbInput]
    split <;> rfl

/-- **Every hash input of the proof's paths is in `log`**: for every path of every phase, the
input of each level from the leaf (`0`) to the root (the path's length). -/
def ClimbInputsIn (h : Bytes → Digest) (proof : Proof) (log : List Bytes) : Prop :=
  ∀ phase ∈ proof.openings, ∀ path ∈ phase, ∀ level ≤ path.path.length,
    climbInput h path level ∈ log

/-- The hash `h`, its input appended to the log. -/
def loggedHash (h : Bytes → Digest) (x : Bytes) : StateM (List Bytes) Digest := do
  modify (· ++ [x])
  pure (h x)

/-- The permutation `F`, logging nothing. -/
def loggedPerm (F : KeccakState → KeccakState) (s : KeccakState) :
    StateM (List Bytes) KeccakState :=
  pure (F s)

end LeanVM.Wire

end
