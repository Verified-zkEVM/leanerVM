/-
  LeanerVM.Protocol.Merkle

  leanVM's Merkle trees over a byte hash: the tree with leaves of `K` words, a phase's pruned
  opening as the verifier checks it and the prover builds it, with completeness, and the reading
  of the verifier's check as VCVio's batch opening for every hash.
-/

module

public import LeanerVM.Protocol.Blake2sHash
public import LeanerVM.Protocol.Blake2sHashFast
public import LeanerVM.Protocol.ToVCVio.Merkle
public import Mathlib.Data.List.Destutter

/-!
# leanVM's Merkle trees

Category B; the compiled verifier checks every Merkle opening of a proof with `merkleVerify`.
The pinned leanVM (`a386121f84292f6fa663aaa3e570c15bc0240ea2`) commits `2^k` rows in
a binary tree over BLAKE2s-256 (`crates/pcs/src/merkle.rs:119-142`, `merkle_tree`): a leaf is the
hash of a row's leaf image as little-endian bytes (`hash_words`), a node the hash of its
children's 64 bytes, left first (`hash_pair`), with no tag and no position
(`crates/fiat_shamir/src/merkle.rs:38-67`). A row narrower than the leaf width is hashed as its
image `zeros ‖ row` (`leaf_image`, `merkle.rs:54-58`; `pcs/src/merkle.rs:161-192`).

Everything here takes the byte hash as a parameter `H`, called for every hash, and the deployed
definitions are its instances at `blake2sBytes`. `merkleVerifyWith` is the verifier's check of a
phase's opening, `PrunedMerklePaths::open` (`merkle.rs:163-235`): the rows at the sorted distinct
queried positions and one list of siblings, bottom-up and left to right (the octopus). In any
monad it calls `H` once per stored row and once per node it rebuilds, in the Rust's order, so
that it can be run with `H` a random-oracle query. Two checks of the Rust are subsumed: the leaf
count is `2^depth` by construction, and an opening of no query fails since the walk has no node to
read at the top. The Rust also returns each query's full path, which is determined by the walk
and dropped here. A prover commits to its rows once (`merkleCommitWith`, which builds the tree's
levels) and reads every opening off the commitment (`merkleOpen`, `PrunedMerklePaths::prune`,
`:101-136`); `merkleVerifyWith_merkleOpen` is completeness.

`merkle_fits` reads the check as VCVio's trees for every hash `H`: it accepts exactly when the
stored rows have the announced shape and the octopus, read by `MerkleTree.toBatchOpening` as a
VCVio `BatchOpening` of `Skeleton.perfect depth`, has VCVio's putative root `root` under the node
hash `fun l r ↦ H (digestBytes l ++ digestBytes r)`, which is `nodeModel`'s query.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters Blake2sHash

@[expose] public section

/-! ## The tree -/

/-- The leaf image of a row of at most `leafWords` words: the row right-aligned, after a zero
prefix (`leaf_image`). A longer row comes back unchanged; the verifier rejects it first. -/
def leafImage (leafWords : ℕ) (row : List K) : List K :=
  List.replicate (leafWords - row.length) 0 ++ row

/-- The bytes a leaf hashes: its words, little-endian (`merkle.rs:61-67`, `hash_words`). -/
def leafBytes (words : List K) : List UInt8 := words.flatMap kBytes

/-- The bytes a node hashes: its children's, left first (`merkle.rs:46-51`, `hash_pair`). -/
def nodeBytes (left right : Digest) : List UInt8 := digestBytes left ++ digestBytes right

/-- The digest of a row's leaf under the byte hash `H`. -/
abbrev leafDigest (H : List UInt8 → Digest) (leafWords : ℕ) (row : List K) : Digest :=
  H (leafBytes (leafImage leafWords row))

/-- The root of the tree over `2^k` leaf images under the byte hash `H` (`merkle_tree`). -/
def merkleRootWith (H : List UInt8 → Digest) {k : ℕ} (leaves : Vector (List K) (2 ^ k)) :
    Digest :=
  MerkleTree.root (fun l r ↦ H (nodeBytes l r)) (fun row ↦ H (leafBytes row)) leaves

/-- The root of the tree over `2^k` leaf images under BLAKE2s-256. -/
def merkleRoot {k : ℕ} (leaves : Vector (List K) (2 ^ k)) : Digest :=
  merkleRootWith blake2sBytes leaves

/-! ## A phase's pruned opening -/

/-- One opening phase's Merkle data (`merkle.rs:88-92`, `PrunedMerklePaths`). -/
structure PrunedMerklePaths where
  /-- The rows at the distinct queried positions, ascending. -/
  leafData : List (List K)
  /-- The siblings of the octopus, bottom-up and left to right. -/
  siblingHashes : List Digest

/-- Query positions ascending, with duplicates removed (`merkle.rs:71-76`, `sorted_unique`):
sorted, then adjacent repeats dropped. -/
def sortedUnique (queries : List ℕ) : List ℕ := queries.mergeSort.destutter (· ≠ ·)

/-- The leaf digests of stored rows under `H`, or `none` at the first row that is not
`rowWords` wide (`merkle.rs:139-150`, `leaf_hashes`). -/
def hashRowsWith {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (rowWords leafWords : ℕ) :
    List (List K) → m (Option (List Digest))
  | [] => pure (some [])
  | row :: rest =>
    if row.length = rowWords then do
      let d ← H (leafBytes (leafImage leafWords row))
      let ds ← hashRowsWith H rowWords leafWords rest
      pure (ds.map (d :: ·))
    else pure none

/-- The rows an accepted opening yields, in query order with duplicates repeated: the leaf image
of the stored row at each query's slot among the sorted distinct positions (`merkle.rs:225-234`).
-/
def rowsInQueryOrder (leafWords : ℕ) (queries : List ℕ) (leafData : List (List K)) :
    List (List K) :=
  let sorted := sortedUnique queries
  queries.map fun q ↦ leafImage leafWords (leafData.getD (sorted.idxOf q) [])

/-- The verifier's check of a phase's pruned opening of the tree of `2^depth` leaves of
`leafWords` words under `root`, at `queries`, with stored rows `rowWords` wide, under the byte
hash `H` (`merkle.rs:163-235`, `PrunedMerklePaths::open`): one stored row per distinct query and
`rowWords ≤ leafWords`, then the rows hashed, each checked for its width, then every query below
the leaf count, then the walk up the octopus, which must use up the siblings and reach `root`.
Returns the rows in query order, or `none`. An accepted opening calls `H` once per stored row and
once per rebuilt node. -/
def merkleVerifyWith {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (root : Digest)
    (depth rowWords leafWords : ℕ) (queries : List ℕ) (paths : PrunedMerklePaths) :
    m (Option (List (List K))) := do
  let sorted := sortedUnique queries
  if sorted.length ≠ paths.leafData.length ∨ leafWords < rowWords then return none
  match ← hashRowsWith H rowWords leafWords paths.leafData with
  | none => return none
  | some leaves =>
    if ∃ p ∈ sorted, 2 ^ depth ≤ p then return none
    match ← MerkleTree.prunedRoot (fun l r ↦ H (nodeBytes l r)) depth (sorted.zip leaves)
        paths.siblingHashes with
    | none => return none
    | some r =>
      return if @decide (r = root) (Digest.decEq r root) then
        some (rowsInQueryOrder leafWords queries paths.leafData)
      else none

/-- The deployed check, under BLAKE2s-256. -/
def merkleVerify (root : Digest) (depth rowWords leafWords : ℕ) (queries : List ℕ)
    (paths : PrunedMerklePaths) : Option (List (List K)) :=
  Id.run (merkleVerifyWith blake2sBytes root depth rowWords leafWords queries paths)

/-- A prover's commitment to `2^k` rows: the rows, and the levels of the tree over their leaf
digests. -/
structure MerkleCommitment (k : ℕ) where
  /-- The committed rows. -/
  rows : Vector (List K) (2 ^ k)
  /-- The tree's levels, from the leaf digests up to the root. -/
  levels : MerkleTree.Levels Digest k

/-- The commitment to `rows`, each hashed as its leaf image under the byte hash `H`, with the
tree built once (`pcs/src/merkle.rs:161-192`, `merkle_tree_padded_rows`). -/
def merkleCommitWith (H : List UInt8 → Digest) (leafWords : ℕ) {k : ℕ}
    (rows : Vector (List K) (2 ^ k)) : MerkleCommitment k where
  rows := rows
  levels := MerkleTree.buildLevels (fun l r ↦ H (nodeBytes l r)) k
    (rows.map (leafDigest H leafWords))

/-- The commitment under BLAKE2s-256. -/
def merkleCommit (leafWords : ℕ) {k : ℕ} (rows : Vector (List K) (2 ^ k)) :
    MerkleCommitment k :=
  merkleCommitWith blake2sBytes leafWords rows

/-- The committed root. -/
def MerkleCommitment.root {k : ℕ} (c : MerkleCommitment k) : Digest := c.levels.root

/-- The prover's pruned opening of a commitment at `queries` (`merkle.rs:101-136`,
`PrunedMerklePaths::prune`): the rows at the sorted distinct positions, and the siblings of
every opened node not paired with the next, read off the committed levels. The Rust pairs a
node with the next when the next is its sibling, which on ascending positions is
`MerkleTree.levelStep`'s test. -/
def merkleOpen {k : ℕ} (c : MerkleCommitment k) (queries : List ℕ) : PrunedMerklePaths where
  leafData := (sortedUnique queries).map fun q ↦ c.rows[q]?.getD []
  siblingHashes := c.levels.siblings (sortedUnique queries)

/-- The committed root is the root of the tree over the rows' leaf images. -/
theorem root_merkleCommitWith (H : List UInt8 → Digest) (leafWords : ℕ) {k : ℕ}
    (rows : Vector (List K) (2 ^ k)) :
    (merkleCommitWith H leafWords rows).root =
      merkleRootWith H (rows.map (leafImage leafWords)) := by
  simp only [MerkleCommitment.root, merkleCommitWith, MerkleTree.root_buildLevels, merkleRootWith,
    MerkleTree.root, Vector.map_map]
  rfl

/-! ## The query model -/

/-- The node hash as a VCVio query model: a node queries its children's 64 bytes, left first,
with no address, on the byte-string oracle the leaves are hashed on. -/
def nodeModel : MerkleTreeExtractability.NodeQueryModel (List UInt8) Unit Digest :=
  MerkleTree.nodeQueryModelOfEncoding digestBytes digestOfBytes 32 length_digestBytes
    digestOfBytes_digestBytes

theorem nodeModel_mkQuery (left right : Digest) :
    nodeModel.mkQuery () (left, right) = nodeBytes left right := rfl

/-! ## The sorted distinct positions -/

private theorem pairwise_mergeSort_le (queries : List ℕ) : queries.mergeSort.Pairwise (· ≤ ·) :=
  (List.pairwise_mergeSort (le := fun a b ↦ decide (a ≤ b))
    (fun _ _ _ h₁ h₂ ↦ decide_eq_true (Nat.le_trans (of_decide_eq_true h₁) (of_decide_eq_true h₂)))
    (fun a b ↦ Bool.or_eq_true_iff.mpr ((Nat.le_total a b).imp decide_eq_true decide_eq_true))
    queries).imp of_decide_eq_true

private theorem sortedUnique_eq_dedup (queries : List ℕ) :
    sortedUnique queries = queries.mergeSort.dedup :=
  (pairwise_mergeSort_le queries).destutter_eq_dedup

theorem mem_sortedUnique {queries : List ℕ} {q : ℕ} : q ∈ sortedUnique queries ↔ q ∈ queries := by
  rw [sortedUnique_eq_dedup, List.mem_dedup, List.mem_mergeSort]

theorem pairwise_sortedUnique (queries : List ℕ) : (sortedUnique queries).Pairwise (· < ·) := by
  rw [sortedUnique_eq_dedup]
  exact (((pairwise_mergeSort_le queries).sublist (List.dedup_sublist _)).and
    (List.nodup_dedup _)).imp fun h ↦ Nat.lt_of_le_of_ne h.1 h.2

theorem sortedUnique_eq_nil {queries : List ℕ} : sortedUnique queries = [] ↔ queries = [] := by
  rw [sortedUnique, List.destutter_eq_nil, ← List.length_eq_zero_iff, List.length_mergeSort,
    List.length_eq_zero_iff]

/-! ## The check in `Id` -/

section RunId

variable (H : List UInt8 → Digest)

/-- The conditions under which the check accepts: one row stored per distinct query, the
announced width at most the leaf width, every row of the announced width, every query in the
tree, and the walk over the siblings reaching `root`. -/
abbrev PrunedMerklePaths.Accepts (paths : PrunedMerklePaths) (root : Digest)
    (depth rowWords leafWords : ℕ) (queries : List ℕ) : Prop :=
  paths.leafData.length = (sortedUnique queries).length ∧ rowWords ≤ leafWords ∧
    (∀ row ∈ paths.leafData, row.length = rowWords) ∧
    (∀ p ∈ sortedUnique queries, p < 2 ^ depth) ∧
    Id.run (MerkleTree.prunedRoot (m := Id) (fun l r ↦ H (nodeBytes l r)) depth
      ((sortedUnique queries).zip (paths.leafData.map (leafDigest H leafWords)))
      paths.siblingHashes) = some root

private theorem run_hashRowsWith (rowWords leafWords : ℕ) :
    ∀ rows : List (List K), Id.run (hashRowsWith (m := Id) H rowWords leafWords rows) =
      if ∀ row ∈ rows, row.length = rowWords then some (rows.map (leafDigest H leafWords))
      else none
  | [] => rfl
  | row :: rest => by
    simp only [hashRowsWith, List.forall_mem_cons]
    by_cases hw : row.length = rowWords
    · simp only [hw, true_and, ↓reduceIte, Id.run_bind, run_hashRowsWith rowWords leafWords rest]
      split <;> rfl
    · simp only [hw, false_and, ↓reduceIte]
      rfl

/-- The check in `Id`: the rows in query order exactly when the stored rows have the announced
shape, the queries lie in the tree, and the walk over the octopus reaches `root`. -/
theorem run_merkleVerifyWith (root : Digest) (depth rowWords leafWords : ℕ) (queries : List ℕ)
    (paths : PrunedMerklePaths) :
    Id.run (merkleVerifyWith (m := Id) H root depth rowWords leafWords queries paths) =
      if paths.Accepts H root depth rowWords leafWords queries then
        some (rowsInQueryOrder leafWords queries paths.leafData)
      else none := by
  simp only [merkleVerifyWith]
  by_cases h1 : (sortedUnique queries).length ≠ paths.leafData.length ∨ leafWords < rowWords
  · rw [ite_eq_left h1, ite_eq_right fun h ↦ by omega]
    rfl
  rw [ite_eq_right h1, Id.run_bind, run_hashRowsWith]
  by_cases hw : ∀ row ∈ paths.leafData, row.length = rowWords
  swap
  · rw [ite_eq_right hw, ite_eq_right fun h ↦ hw h.2.2.1]
    rfl
  rw [ite_eq_left hw]
  dsimp only
  by_cases hr : ∃ p ∈ sortedUnique queries, 2 ^ depth ≤ p
  · have ⟨p, hp, hle⟩ := hr
    rw [ite_eq_left hr, ite_eq_right fun h ↦ Nat.not_lt.mpr hle (h.2.2.2.1 p hp)]
    rfl
  rw [ite_eq_right hr, Id.run_bind]
  replace hr : ∀ p ∈ sortedUnique queries, p < 2 ^ depth :=
    fun p hp ↦ Nat.lt_of_not_le fun hle ↦ hr ⟨p, hp, hle⟩
  unfold PrunedMerklePaths.Accepts
  rcases Id.run (MerkleTree.prunedRoot (m := Id) (fun l r ↦ H (nodeBytes l r)) depth
    ((sortedUnique queries).zip (paths.leafData.map (leafDigest H leafWords)))
    paths.siblingHashes) with _ | r
  · exact (ite_eq_right fun h ↦ nomatch h.2.2.2.2).symm
  by_cases hroot : r = root
  · subst hroot
    rw [ite_eq_left ⟨by omega, by omega, hw, hr, rfl⟩]
    exact ite_eq_left (@decide_eq_true _ (Digest.decEq r r) rfl)
  · rw [ite_eq_right fun h ↦ hroot (Option.some.inj h.2.2.2.2)]
    exact ite_eq_right fun h ↦ hroot (@of_decide_eq_true _ (Digest.decEq r root) h)

/-- The check read as VCVio's trees, for every byte hash `H`: an opening is accepted with `rows`
exactly when one row is stored per distinct query, each `rowWords ≤ leafWords` wide, `rows` are
their leaf images in query order, and the octopus, read as a VCVio batch opening of the perfect
tree of depth `depth` with the stored rows' leaf digests at the sorted distinct queries, has
VCVio's putative root `root` under the node hash on the children's bytes (`nodeModel`'s query).
-/
theorem merkle_fits (root : Digest) (depth rowWords leafWords : ℕ) (queries : List ℕ)
    (paths : PrunedMerklePaths) (rows : List (List K)) :
    Id.run (merkleVerifyWith (m := Id) H root depth rowWords leafWords queries paths) =
        some rows ↔
      (paths.leafData.length = (sortedUnique queries).length ∧ rowWords ≤ leafWords ∧
        (∀ row ∈ paths.leafData, row.length = rowWords) ∧
        rows = rowsInQueryOrder leafWords queries paths.leafData) ∧
      ∃ o, MerkleTree.toBatchOpening depth (sortedUnique queries)
          (paths.leafData.map (leafDigest H leafWords)) paths.siblingHashes = some o ∧
        InductiveMerkleTree.getPutativeBatchRootWithHash
          (fun l r ↦ H (digestBytes l ++ digestBytes r)) o.values o.proof = root := by
  rw [run_merkleVerifyWith, Option.ite_none_right_eq_some, Option.some_inj]
  refine .trans ?_ (Iff.rfl.and (MerkleTree.prunedRoot_eq_some_iff
    (fun l r ↦ H (nodeBytes l r)) depth _ _ _ root).symm)
  exact ⟨fun ⟨hc, h⟩ ↦ ⟨⟨hc.1, hc.2.1, hc.2.2.1, h.symm⟩,
      ⟨pairwise_sortedUnique _, hc.2.2.2.1, by rw [List.length_map, hc.1]⟩, hc.2.2.2.2⟩,
    fun ⟨⟨h1, h2, h3, h⟩, ⟨_, h4, _⟩, h5⟩ ↦ ⟨⟨h1, h2, h3, h4, h5⟩, h.symm⟩⟩

private theorem nodesAt_map {k : ℕ} (rows : Vector (List K) (2 ^ k)) (f : List K → Digest) :
    ∀ ps : List ℕ, (∀ p ∈ ps, p < 2 ^ k) →
      MerkleTree.nodesAt (rows.map f) ps = ps.zip ((ps.map fun q ↦ rows[q]?.getD []).map f)
  | [], _ => rfl
  | p :: ps, h => by
    obtain ⟨hp, hps⟩ := List.forall_mem_cons.mp h
    rw [MerkleTree.nodesAt_cons _ hp, nodesAt_map rows f ps hps]
    simp [hp]

/-- Completeness: the commitment to `rows`, each `rowWords ≤ leafWords` wide, opened at
nonempty queries in the tree, is accepted under its root, with the queried rows' leaf images in
query order. -/
theorem merkleVerifyWith_merkleOpen {k rowWords leafWords : ℕ}
    (rows : Vector (List K) (2 ^ k)) (queries : List ℕ) (hrw : rowWords ≤ leafWords)
    (hw : ∀ row ∈ rows.toList, row.length = rowWords) (hne : queries ≠ [])
    (hlt : ∀ q ∈ queries, q < 2 ^ k) :
    Id.run (merkleVerifyWith (m := Id) H (merkleCommitWith H leafWords rows).root k rowWords
        leafWords queries (merkleOpen (merkleCommitWith H leafWords rows) queries)) =
      some (queries.map fun q ↦ leafImage leafWords (rows[q]?.getD [])) := by
  have hslt : ∀ p ∈ sortedUnique queries, p < 2 ^ k := fun p hp ↦ hlt p (mem_sortedUnique.mp hp)
  have hoct := MerkleTree.prunedRoot_openSiblings (fun l r ↦ H (nodeBytes l r))
    (rows.map (leafDigest H leafWords)) (sortedUnique queries) (mt sortedUnique_eq_nil.mp hne) hslt
  rw [nodesAt_map rows _ _ hslt, ← MerkleTree.siblings_buildLevels,
    ← MerkleTree.root_buildLevels] at hoct
  rw [run_merkleVerifyWith, ite_eq_left]
  · refine congrArg some (List.map_congr_left fun q hq ↦ ?_)
    have hmem : q ∈ sortedUnique queries := mem_sortedUnique.mpr hq
    rw [List.getD_eq_getElem?_getD, merkleOpen, List.getElem?_map,
      List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem), List.getElem_idxOf]
    rfl
  · refine ⟨by simp [merkleOpen], hrw, fun row hrow ↦ ?_, hslt, hoct⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hrow
    rw [Vector.getElem?_eq_getElem (hslt q hq), Option.getD_some]
    exact hw _ (by simp [merkleCommitWith])

end RunId

end
end LeanerVM.Protocol
