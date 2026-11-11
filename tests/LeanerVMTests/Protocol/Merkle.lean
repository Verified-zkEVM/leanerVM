import LeanerVM.Protocol.Merkle

/-!
# Merkle tree tests

A four-leaf tree of two-word leaves against a tree computed with CPython's `hashlib.blake2s`
(leaf `q` holds the words `2q + 1, 2q + 2`): the leaf digests, a node and the root. Then the
octopus of the pinned leanVM's tests (`fiat_shamir/src/merkle.rs:283-351`): eight leaves of four
words, row `q` holding `4q, …, 4q + 3`, opened at the queries `[5, 1, 5, 3, 1]` and `[5, 1, 3]`;
the root and the siblings are `hashlib`'s, with the Rust's `tree_of` and `prune` transcribed
(`merkle.rs:101-136, 270-281`). The prover's opening equals the Rust's, the check accepts it with
the rows in query order and nine hash calls, and every malformed phase of the Rust's test is
rejected, except the tree of seven leaves, which a depth cannot express. The same rows over
sixteen leaves are opened at `[0, 1, 2, 3, 7, 8, 15, 15, 4, 9]`, with pairs at every level.

Each check of `merkleVerifyWith` has a mutation that only it rejects. The check is the
conjunction of five conditions (`run_merkleVerifyWith`), and `conds` evaluates each; for every
mutation exactly the targeted condition fails, so the check without it would accept. The walk's
own checks are separated by `climb`, the walk without its final read: a surplus sibling is the
only defect of its opening, a missing one stops the walk, and a flipped one reaches another root.

The reading as VCVio's trees: `toBatchOpening` of the octopus has VCVio's putative root equal to
the Rust's root and selects the queried leaves in VCVio's leaf order; a surplus or missing
sibling, an out-of-range or unsorted position and a position count other than the row count have
no reading, and a flipped sibling or row reads with another root. Last, the node query model, a
node opened as a leaf, and the leaf image.
-/

namespace LeanerVMTests.Protocol.Merkle

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash

/-- The word `n`. -/
def w (n : ℕ) : K := K.ofBits n

/-! ## A four-leaf tree -/

/-- Four leaves of two words each. -/
def leaves : Vector (List K) (2 ^ 2) := #v[[w 1, w 2], [w 3, w 4], [w 5, w 6], [w 7, w 8]]

def leaf0 : Digest :=
  #v[0x6b8928f2, 0x12389f83, 0xe4753c2b, 0x44f83b7f, 0x926dae68, 0xa0cb51b5, 0x1828562e, 0x44a89c61]

def leaf2 : Digest :=
  #v[0xeacefdb4, 0x9e397c69, 0xbcf9f243, 0xc7f40b56, 0x826da590, 0x3bb84405, 0xe99b0a9f, 0x03750514]

def leaf3 : Digest :=
  #v[0x9bab6c86, 0x345166bc, 0x5730c074, 0xc2393427, 0x9ef39974, 0x6dfecedf, 0xbd896888, 0x73752516]

/-- The parent of leaves 0 and 1. -/
def node01 : Digest :=
  #v[0x01a94e81, 0x0420c37d, 0xb019f25c, 0xdde39305, 0xfd847b9b, 0x4ca593a1, 0x94752d9b, 0x5860fd80]

def root : Digest :=
  #v[0x7e356111, 0x24253a30, 0x0b7ce2b6, 0xafccea2e, 0xc18c3ac5, 0x780bb6f6, 0xa9d96af7, 0x34ae5f2d]

#guard hashWords [w 1, w 2] = leaf0
#guard hashWords [w 5, w 6] = leaf2
#guard hashWords [w 7, w 8] = leaf3
#guard hashPair leaf0 (hashWords [w 3, w 4]) = node01
#guard merkleRoot leaves = root

/- The leaf and node hashes of `merkleRootWith` at `blake2sBytes` are `hash_words` and
`hash_pair`. -/
#guard blake2sBytes (leafBytes [w 5, w 6]) = hashWords [w 5, w 6]
#guard blake2sBytes (nodeBytes leaf0 leaf3) = hashPair leaf0 leaf3

/-! ## The Rust's octopus -/

/-- Row `q` of the eight-leaf tree: the words `4q, …, 4q + 3`. -/
def row (q : ℕ) : List K := (List.range 4).map fun j ↦ w (4 * q + j)

def rows8 : Vector (List K) (2 ^ 3) := Vector.ofFn fun q ↦ row q

def root8 : Digest :=
  #v[0x683740ce, 0x4c08ee81, 0x0c851c06, 0xa9800368, 0x28da23a1, 0x751fe579, 0x83a776d8, 0x91ed3198]

/-- Leaves 0, 2 and 4, the parent of leaves 6 and 7, and the right child of the root. -/
def h0 : Digest :=
  #v[0xcc2800a6, 0xebc2a333, 0xee339081, 0x0dacd599, 0xedfc74c9, 0x86c31cb2, 0xa3ed6c35, 0x853ffc44]

def h2 : Digest :=
  #v[0x6e19d701, 0x6ff8ca94, 0x14ebf858, 0x14d62ead, 0x22e980c3, 0x8557a2b4, 0x94551dc0, 0x21c73c78]

def h4 : Digest :=
  #v[0x93fbee2a, 0x7802b02c, 0xe5c7abb9, 0x8faa9032, 0x9560ed0c, 0x2f7cedb7, 0x677d1d65, 0xda057af1]

def n67 : Digest :=
  #v[0x82f95979, 0x31167920, 0x9d5afc9e, 0xd74a158f, 0x86daf687, 0x2fc6e44f, 0x601febc2, 0xa6723d22]

def n4567 : Digest :=
  #v[0xa649a43c, 0xaf7241d2, 0xd89ec50c, 0x4446ba2d, 0x8d02e9bc, 0xf64df591, 0x12145fbf, 0xf7beea31]

/-- The Rust's octopus at the positions `1, 3, 5`: the siblings of leaves 1, 3 and 5, then the
sibling of their parent at index 2; the parents at 0 and 1 pair, and so do the next two. -/
def octopus : List Digest := [h0, h2, h4, n67]

def good : PrunedMerklePaths := ⟨[row 1, row 3, row 5], octopus⟩

/-- The prover's commitment to the eight rows. -/
def commit8 : MerkleCommitment 3 := merkleCommit 4 rows8

#guard merkleRoot rows8 = root8
#guard commit8.root = root8

/- The prover's opening is the Rust's, for both query lists. -/
#guard (merkleOpen commit8 [5, 1, 5, 3, 1]).leafData = good.leafData
#guard (merkleOpen commit8 [5, 1, 5, 3, 1]).siblingHashes = octopus
#guard (merkleOpen commit8 [5, 1, 3]).siblingHashes = octopus

/- Accepted, with the rows in query order, duplicates repeated. -/
#guard merkleVerify root8 3 4 4 [5, 1, 5, 3, 1] good = some [row 5, row 1, row 5, row 3, row 1]
#guard merkleVerify root8 3 4 4 [5, 1, 3] good = some [row 5, row 1, row 3]

/-- The byte hash with a counter of its calls. -/
def countingHash (b : List UInt8) : StateM ℕ Digest := do
  modify (· + 1)
  pure (blake2sBytes b)

/- Nine calls: three stored rows and the six nodes rebuilt (three, two, one per level). -/
#guard (Id.run ((merkleVerifyWith countingHash root8 3 4 4 [5, 1, 5, 3, 1] good).run 0)).2 = 9

/-! ## Sixteen leaves, pairs at every level

The same rows over sixteen leaves, opened at `[0, 1, 2, 3, 7, 8, 15, 15, 4, 9]`: unsorted, with
a duplicate, and with paired nodes at every level. The root and the five siblings are `hashlib`'s,
from the Rust's `tree_of` and `prune` transcribed. -/

def rows16 : Vector (List K) (2 ^ 4) := Vector.ofFn fun q ↦ row q

def root16 : Digest :=
  #v[0x2a0bcfc4, 0x9bba018e, 0xc78bd5fa, 0xa6fb1e86, 0x212c6d33, 0x50e2f351, 0x377c4ba3, 0x43efd537]

/-- Leaves 5, 6 and 14, and the parents of leaves 10 and 11 and of leaves 12 and 13. -/
def g5 : Digest :=
  #v[0xb95f5899, 0x1687203e, 0x0a25ae87, 0xeb3571b6, 0xb01d05e0, 0x9b5920e1, 0x571e611d, 0x18be896c]

def g6 : Digest :=
  #v[0xf8de964c, 0x8d4f8c9c, 0x73014154, 0x074b82e0, 0xf1aad3df, 0x755b15ba, 0x847c554c, 0xf47bb47a]

def g14 : Digest :=
  #v[0xb494480a, 0xf6769b5b, 0xe458aa93, 0x4d751a23, 0xff3d01cc, 0x5100d875, 0xcf303851, 0x9bb119e1]

def g1011 : Digest :=
  #v[0x7a4676b7, 0xc3e3180f, 0x24762491, 0xa03d6fa6, 0x491f5bdf, 0xc07b50fc, 0x3fbf567f, 0x33d29eca]

def g1213 : Digest :=
  #v[0x2082992c, 0xf79a9da3, 0x6d036739, 0xfbcc5612, 0xb16481e1, 0x32079311, 0x69a1fef2, 0x68d282b9]

/-- The Rust's octopus at `[0, 1, 2, 3, 7, 8, 15, 15, 4, 9]`: the siblings of leaves 4, 7 and 15,
then of the level-1 nodes 4 and 7; the other nodes pair at every level. -/
def octopus16 : List Digest := [g5, g6, g14, g1011, g1213]

def queries16 : List ℕ := [0, 1, 2, 3, 7, 8, 15, 15, 4, 9]

def commit16 : MerkleCommitment 4 := merkleCommit 4 rows16

#guard commit16.root = root16
#guard sortedUnique queries16 = [0, 1, 2, 3, 4, 7, 8, 9, 15]
#guard (merkleOpen commit16 queries16).siblingHashes = octopus16
#guard merkleVerify root16 4 4 4 queries16 (merkleOpen commit16 queries16) =
  some (queries16.map row)
#guard (MerkleTree.toBatchOpening 4 (sortedUnique queries16)
    (((sortedUnique queries16).map row).map (leafDigest blake2sBytes 4)) octopus16).map
    (MerkleTree.putativeRoot hashPair) = some root16

/-! ## Malformed phases

`conds` lists the five conditions of the check: one row per distinct query, the announced width
at most the leaf width, every row of the announced width, every query in the tree, and the walk
reaching the root. -/

def conds (root : Digest) (depth rowWords leafWords : ℕ) (queries : List ℕ)
    (paths : PrunedMerklePaths) : List Bool :=
  let sorted := sortedUnique queries
  [decide (paths.leafData.length = sorted.length), decide (rowWords ≤ leafWords),
    paths.leafData.all (·.length == rowWords), sorted.all (· < 2 ^ depth),
    Id.run (MerkleTree.prunedRoot (m := Id) (fun l r ↦ blake2sBytes (nodeBytes l r)) depth
      (sorted.zip (paths.leafData.map (leafDigest blake2sBytes leafWords)))
      paths.siblingHashes) == some root]

/- The honest phase meets all five. -/
#guard conds root8 3 4 4 [5, 1, 3] good = [true, true, true, true, true]

/-- The walk over `k` levels without its final read: the top level and the siblings left. -/
def climb : ℕ → List (ℕ × Digest) → List Digest → Option (List (ℕ × Digest) × List Digest)
  | 0, nodes, sibs => some (nodes, sibs)
  | k + 1, nodes, sibs =>
    (Id.run (MerkleTree.levelStep (MerkleTree.NodeAlgebra.ofHash (m := Id) hashPair) (h := 0)
      nodes sibs)).bind fun r ↦ climb k r.1 r.2

/-- The opened leaves at the positions `1, 3, 5`. -/
def leaves135 : List (ℕ × Digest) :=
  [(1, hashWords (row 1)), (3, hashWords (row 3)), (5, hashWords (row 5))]

#guard climb 3 leaves135 octopus = some ([(0, root8)], [])

def zeroDigest : Digest := #v[0, 0, 0, 0, 0, 0, 0, 0]

/-- A digest with its first byte flipped. -/
def flip (d : Digest) : Digest := d.set 0 (d[0] ^^^ 1)

/- A surplus sibling: the walk reaches the root and only the sibling left over rejects it. -/
#guard merkleVerify root8 3 4 4 [5, 1, 3] ⟨good.leafData, octopus ++ [zeroDigest]⟩ = none
#guard climb 3 leaves135 (octopus ++ [zeroDigest]) = some ([(0, root8)], [zeroDigest])

/- A missing sibling: the walk runs out. -/
#guard merkleVerify root8 3 4 4 [5, 1, 3] ⟨good.leafData, octopus.dropLast⟩ = none
#guard climb 3 leaves135 octopus.dropLast = none

/- A flipped sibling: the walk uses every sibling and reaches another root. -/
#guard merkleVerify root8 3 4 4 [5, 1, 3] ⟨good.leafData, flip h0 :: octopus.tail⟩ = none
#guard match climb 3 leaves135 (flip h0 :: octopus.tail) with
  | some ([(0, r)], []) => r != root8
  | _ => false

/- A flipped row, and a row one word wide. -/
#guard merkleVerify root8 3 4 4 [5, 1, 3] ⟨[[w 5, w 5, w 6, w 7], row 3, row 5], octopus⟩ = none
#guard conds root8 3 4 4 [5, 1, 3] ⟨[[w 5, w 5, w 6, w 7], row 3, row 5], octopus⟩ =
  [true, true, true, true, false]
#guard merkleVerify root8 3 4 4 [5, 1, 3] ⟨[row 1 ++ [w 0], row 3, row 5], octopus⟩ = none

/- A wrong announced width, a wrong query count, an out-of-range query. -/
#guard merkleVerify root8 3 5 5 [5, 1, 3] good = none
#guard merkleVerify root8 3 4 4 [5, 1] good = none
#guard merkleVerify root8 3 4 4 [9, 1, 3] good = none

/- No query: the walk has no node at the top. -/
#guard merkleVerify root8 3 4 4 [] ⟨[], []⟩ = none
#guard merkleVerify root8 0 4 4 [] ⟨[], []⟩ = none

/-! ## Each condition is load-bearing -/

/- A surplus row: only the count rejects it, since the walk zips the positions with the rows. -/
#guard merkleVerify root8 3 4 4 [5, 1, 3] ⟨good.leafData ++ [row 7], octopus⟩ = none
#guard conds root8 3 4 4 [5, 1, 3] ⟨good.leafData ++ [row 7], octopus⟩ =
  [false, true, true, true, true]

/- An announced width above the leaf width: the leaf image of a four-word row in three-word
leaves is the row, so only the width bound rejects it. -/
#guard merkleVerify root8 3 4 3 [5, 1, 3] good = none
#guard conds root8 3 4 3 [5, 1, 3] good = [true, false, true, true, true]

/- An announced width below the rows': the leaf images are the rows, so only the row width
rejects it. -/
#guard merkleVerify root8 3 3 4 [5, 1, 3] good = none
#guard conds root8 3 3 4 [5, 1, 3] good = [true, true, false, true, true]

/-- An opening at the positions `1, 3, 13` with row 5 stored at 13: read modulo the tree, 13 is
leaf 5, and with the siblings of the walk's shape, the last a junk sibling of a node beside the
root, the walk's first node at the top is the root. -/
def outOfRange : PrunedMerklePaths := ⟨good.leafData, [h0, h2, h4, n67, n4567, h0]⟩

#guard merkleVerify root8 3 4 4 [1, 3, 13] outOfRange = none
#guard conds root8 3 4 4 [1, 3, 13] outOfRange = [true, true, true, false, true]

/- The walk's three checks are the surplus, missing and flipped siblings above. -/
#guard conds root8 3 4 4 [5, 1, 3] ⟨good.leafData, octopus ++ [zeroDigest]⟩ =
  [true, true, true, true, false]
#guard conds root8 3 4 4 [5, 1, 3] ⟨good.leafData, octopus.dropLast⟩ =
  [true, true, true, true, false]
#guard conds root8 3 4 4 [5, 1, 3] ⟨good.leafData, flip h0 :: octopus.tail⟩ =
  [true, true, true, true, false]

/-! ## The reading as VCVio's trees -/

/-- VCVio's putative root of the octopus read at `positions` with the leaf digests of `rows`. -/
def readRoot (positions : List ℕ) (rows : List (List K)) (sibs : List Digest) : Option Digest :=
  (MerkleTree.toBatchOpening 3 positions (rows.map (leafDigest blake2sBytes 4)) sibs).map
    (MerkleTree.putativeRoot hashPair)

#guard readRoot [1, 3, 5] good.leafData octopus = some root8

/- The reading selects leaves 1, 3 and 5 in VCVio's leaf order. -/
#guard ((MerkleTree.toBatchOpening 3 [1, 3, 5] (good.leafData.map (leafDigest blake2sBytes 4))
    octopus).map fun o ↦
      (List.range 8).map fun p ↦ o.selector.get (BinaryTree.SkeletonLeafIndex.ofNat 3 p)) =
  some [false, true, false, true, false, true, false, false]

/- No reading of a surplus or missing sibling, an out-of-range or unsorted position, or a
position count that is not the row count. -/
#guard readRoot [1, 3, 5] good.leafData (octopus ++ [zeroDigest]) = none
#guard readRoot [1, 3, 5] good.leafData octopus.dropLast = none
#guard readRoot [1, 3, 13] good.leafData outOfRange.siblingHashes = none
#guard readRoot [3, 1, 5] good.leafData octopus = none
#guard readRoot [1, 3] good.leafData octopus = none

/- A flipped sibling or row has a reading, with another root. -/
#guard (readRoot [1, 3, 5] good.leafData (flip h0 :: octopus.tail)).isSome
#guard readRoot [1, 3, 5] good.leafData (flip h0 :: octopus.tail) != some root8
#guard readRoot [1, 3, 5] [[w 5, w 5, w 6, w 7], row 3, row 5] octopus != some root8

/- The node query model: a node queries its children's bytes and reads them back. -/
#guard nodeModel.mkQuery () (leaf0, leaf3) = nodeBytes leaf0 leaf3
#guard nodeModel.view.input (nodeModel.mkQuery () (leaf0, leaf3)) = (leaf0, leaf3)
#guard blake2sBytes (nodeModel.mkQuery () (leaf0, leaf3)) = hashPair leaf0 leaf3

/-! ## A node opened as a leaf -/

/-- The eight words whose bytes are the digests of leaves 2 and 3: as a row they hash to the
parent of those leaves, since a leaf of eight words and a pair of digests are the same 64 bytes
to BLAKE2s. -/
def nodeAsLeaf : List K :=
  [ofWords leaf2[0] leaf2[1], ofWords leaf2[2] leaf2[3], ofWords leaf2[4] leaf2[5],
   ofWords leaf2[6] leaf2[7], ofWords leaf3[0] leaf3[1], ofWords leaf3[2] leaf3[3],
   ofWords leaf3[4] leaf3[5], ofWords leaf3[6] leaf3[7]]

#guard hashWords nodeAsLeaf = hashPair leaf2 leaf3

/- Against the four-leaf tree of two-word leaves the width rejects it, and at the eight-word width
the walk runs out of siblings a level short; against a two-leaf tree of eight-word leaves it is
the honest opening of leaf 1. -/
#guard merkleVerify root 2 2 2 [1] ⟨[nodeAsLeaf], [node01]⟩ = none
#guard merkleVerify root 2 8 8 [1] ⟨[nodeAsLeaf], [node01]⟩ = none
#guard merkleVerify root 1 8 8 [1] ⟨[nodeAsLeaf], [node01]⟩ = some [nodeAsLeaf]

/-! ## The leaf image and the sibling index -/

/- A two-word row in a four-word leaf: two zero words first. -/
#guard leafImage 4 [w 7, w 8] = [0, 0, w 7, w 8]

/- Its digest, from `hashlib` on the 32 bytes `0 … 0, 07, 0 …, 08, 0 …`. -/
#guard hashWords (leafImage 4 [w 7, w 8]) =
  #v[0x3b711e04, 0xe64bb3a0, 0x1dee79f2, 0x378ad753, 0xbb717a8c, 0xd0e4ccc2, 0x66e2f70e, 0xb9a04311]

/- A row already of the leaf width is unchanged. -/
#guard leafImage 2 [w 7, w 8] = [w 7, w 8]

/- Two-word rows committed in four-word leaves: each row is stored as is and opened against the
tree of its leaf images, and the check returns the images. -/
#guard (merkleCommit 4 leaves).root = merkleRoot (leaves.map (leafImage 4))
#guard merkleVerify (merkleCommit 4 leaves).root 2 2 4 [2, 0]
    (merkleOpen (merkleCommit 4 leaves) [2, 0]) = some [[0, 0, w 5, w 6], [0, 0, w 1, w 2]]
#guard (merkleOpen (merkleCommit 4 leaves) [2, 0]).leafData = [[w 1, w 2], [w 5, w 6]]

example : ∀ i < 16, MerkleTree.sibling i = i ^^^ 1 := by decide

end LeanerVMTests.Protocol.Merkle
