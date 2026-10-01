/-
  LeanerVM.Protocol.Merkle

  leanVM's Merkle trees: the generic tree over BLAKE2s-256 with leaves of `K` words, the leaf
  image with its zero prefix, and the verifier's path check.
-/

module

public import LeanerVM.Protocol.Blake2sHash
public import LeanerVM.Protocol.ToArkLib.Merkle

/-!
# leanVM's Merkle trees

Category B. The committer's tree is `crates/pcs/src/merkle.rs:119-142` (`merkle_tree`) of the
pinned leanVM (`a386121f84292f6fa663aaa3e570c15bc0240ea2`): `2^k` leaves hashed by `hash_words`,
parents by `hash_pair`, left child first, up to one root. A leaf is a row of `K` words; a row
narrower than the leaf width is hashed as its image `zeros ‖ row`, the zero prefix being what a
commitment with absent lanes leaves out of the proof (`fiat_shamir/src/merkle.rs:54-58`,
`leaf_image`; `pcs/src/merkle.rs:161-192`). The verifier's check is `RawMerklePath::root`
(`fiat_shamir/src/merkle.rs:254-263`): climb the sibling path from the leaf's digest, the running
node on the left at an even index, and compare with the root. The pruned form in which a proof
carries the paths of one level's queries (`PrunedMerklePaths`) is the proof object's, not this
module's.

`merkleVerify_merklePath` is the completeness of the check; `collision_of_merkleVerify` is the
binding half, two accepted openings that disagree exhibit a collision of `hashWords` or
`hashPair`, both instances of the generic facts of `LeanerVM.Protocol.ToArkLib.Merkle`.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters Blake2sHash

@[expose] public section

/-- The leaf image of a row of at most `leafWords` words: the row right-aligned, after a zero
prefix (`leaf_image`). -/
def leafImage (leafWords : ℕ) (row : List K) : List K :=
  List.replicate (leafWords - row.length) 0 ++ row

/-- The Merkle root of `2^k` leaves of `K` words (`merkle_tree`). -/
def merkleRoot {k : ℕ} (leaves : Vector (List K) (2 ^ k)) : Digest :=
  MerkleTree.root hashWords hashPair leaves

/-- The authentication path of leaf `i`: its siblings, leaf level first. -/
def merklePath {k : ℕ} (leaves : Vector (List K) (2 ^ k)) (i : Fin (2 ^ k)) : List Digest :=
  MerkleTree.path hashWords hashPair leaves i

/-- The verifier's check: the path from the leaf at `index` climbs to `root`
(`RawMerklePath::root`, compared with the root the transcript holds). -/
def merkleVerify (root : Digest) (index : ℕ) (leaf : List K) (path : List Digest) : Bool :=
  @MerkleTree.verify _ _ hashWords hashPair Digest.decEq root index leaf path

/-- Completeness: every leaf of a tree is accepted under its root with its path. -/
theorem merkleVerify_merklePath {k : ℕ} (leaves : Vector (List K) (2 ^ k)) (i : Fin (2 ^ k)) :
    merkleVerify (merkleRoot leaves) i leaves[i] (merklePath leaves i) = true :=
  @MerkleTree.verify_path _ _ hashWords hashPair Digest.decEq k leaves i

/-- Two accepted openings of one root at one index with different leaves and paths of equal
length exhibit a collision of the leaf hash or of the node hash. -/
theorem collision_of_merkleVerify {root : Digest} {leaf leaf' : List K} {i : ℕ}
    {p p' : List Digest} (hl : p.length = p'.length) (hne : leaf ≠ leaf')
    (h : merkleVerify root i leaf p = true) (h' : merkleVerify root i leaf' p' = true) :
    MerkleTree.LeafCollision hashWords ∨ MerkleTree.PairCollision hashPair :=
  @MerkleTree.collision_of_verify _ _ hashWords hashPair Digest.decEq root leaf leaf' i p p'
    hl hne h h'

end
end LeanerVM.Protocol
