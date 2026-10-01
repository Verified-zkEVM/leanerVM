import LeanerVM.Protocol.Merkle

/-!
# Merkle tree tests

A four-leaf tree of two-word leaves against a tree computed with CPython's `hashlib.blake2s`
(leaf `q` holds the words `2q + 1, 2q + 2`): the leaf digests, the root, and the path of leaf 2;
the verifier accepting that path, and rejecting a tampered sibling, a wrong index, a tampered
row, a short path, a long path and a wrong root (`fiat_shamir/src/merkle.rs`, the test
`malformed_phases_are_rejected`); the zero-prefix leaf image; and the sibling index as
`i ^^^ 1`, the form the pinned source uses (`merkle.rs:117, 120, 218`).
-/

namespace LeanerVMTests.Protocol.Merkle

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash

/-- The word `n`. -/
def w (n : ℕ) : K := K.ofBits n

/-- Four leaves of two words each. -/
def leaves : Vector (List K) (2 ^ 2) := #v[[w 1, w 2], [w 3, w 4], [w 5, w 6], [w 7, w 8]]

def leaf0 : Digest :=
  #v[0x6b8928f2, 0x12389f83, 0xe4753c2b, 0x44f83b7f, 0x926dae68, 0xa0cb51b5, 0x1828562e, 0x44a89c61]

def leaf3 : Digest :=
  #v[0x9bab6c86, 0x345166bc, 0x5730c074, 0xc2393427, 0x9ef39974, 0x6dfecedf, 0xbd896888, 0x73752516]

/-- The parent of leaves 0 and 1. -/
def node01 : Digest :=
  #v[0x01a94e81, 0x0420c37d, 0xb019f25c, 0xdde39305, 0xfd847b9b, 0x4ca593a1, 0x94752d9b, 0x5860fd80]

def root : Digest :=
  #v[0x7e356111, 0x24253a30, 0x0b7ce2b6, 0xafccea2e, 0xc18c3ac5, 0x780bb6f6, 0xa9d96af7, 0x34ae5f2d]

/-- The path of leaf 2: its sibling leaf 3, then the parent of leaves 0 and 1. -/
def path2 : List Digest := [leaf3, node01]

/-! ## The honest tree -/

#guard hashWords [w 1, w 2] = leaf0
#guard hashWords [w 7, w 8] = leaf3
#guard hashPair leaf0 (hashWords [w 3, w 4]) = node01
#guard merkleRoot leaves = root
#guard merklePath leaves ⟨2, by decide⟩ = path2
#guard merkleVerify root 2 [w 5, w 6] path2 = true

/-- The same acceptance, decided in the kernel. -/
example : merkleVerify root 2 [w 5, w 6] path2 = true := by decide +kernel

/-! ## Mutations rejected -/

/- A tampered sibling. -/
#guard merkleVerify root 2 [w 5, w 6] [leaf3.set 0 (leaf3[0] ^^^ 1), node01] = false

/- The right leaf at the wrong index: the sibling order flips. -/
#guard merkleVerify root 3 [w 5, w 6] path2 = false

/- A tampered row. -/
#guard merkleVerify root 2 [w 5, w 7] path2 = false

/- A path one sibling short. -/
#guard merkleVerify root 2 [w 5, w 6] [node01] = false

/- A path one sibling long. -/
#guard merkleVerify root 2 [w 5, w 6] [leaf3, node01, node01] = false

/- A wrong root. -/
#guard merkleVerify (root.set 0 0) 2 [w 5, w 6] path2 = false

/-! ## The leaf image and the sibling index -/

/- A two-word row in a four-word leaf: two zero words first. -/
#guard leafImage 4 [w 7, w 8] = [0, 0, w 7, w 8]

/- Its digest, from `hashlib` on the 32 bytes `0 … 0, 07, 0 …, 08, 0 …`. -/
#guard hashWords (leafImage 4 [w 7, w 8]) =
  #v[0x3b711e04, 0xe64bb3a0, 0x1dee79f2, 0x378ad753, 0xbb717a8c, 0xd0e4ccc2, 0x66e2f70e, 0xb9a04311]

/- A row already of the leaf width is unchanged. -/
#guard leafImage 2 [w 7, w 8] = [w 7, w 8]

example : ∀ i < 16, MerkleTree.sibling i = i ^^^ 1 := by decide

end LeanerVMTests.Protocol.Merkle
