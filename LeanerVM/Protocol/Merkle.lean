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
public import Mathlib.Data.List.Dedup

/-!
# leanVM's Merkle trees

Category B. The pinned leanVM (`a386121f84292f6fa663aaa3e570c15bc0240ea2`) commits `2^k` rows in
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
and dropped here. `merkleOpenWith` is the prover (`PrunedMerklePaths::prune`, `:101-136`), and
`merkleVerifyWith_merkleOpenWith` its completeness.

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

/-- Query positions ascending, with duplicates removed (`merkle.rs:71-76`, `sorted_unique`). -/
def sortedUnique (queries : List ℕ) : List ℕ := queries.mergeSort.dedup

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
  queries.map fun q ↦ leafImage leafWords (leafData.getD ((sortedUnique queries).idxOf q) [])

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
    match ← MerkleTree.octopusRoot (fun l r ↦ H (nodeBytes l r)) depth (sorted.zip leaves)
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

/-- The prover's pruned opening of the tree over `rows`, each hashed as its leaf image, at
`queries` (`merkle.rs:101-136`, `PrunedMerklePaths::prune`): the rows at the sorted distinct
positions, and the siblings of every opened node not paired with the next. The Rust pairs a
node with the next when the next is its sibling, which on ascending positions is
`MerkleTree.levelStep`'s test. -/
def merkleOpenWith (H : List UInt8 → Digest) (leafWords : ℕ) {k : ℕ}
    (rows : Vector (List K) (2 ^ k)) (queries : List ℕ) : PrunedMerklePaths where
  leafData := (sortedUnique queries).map fun q ↦ rows[q]?.getD []
  siblingHashes := MerkleTree.openSiblings (fun l r ↦ H (nodeBytes l r)) k
    (rows.map (leafDigest H leafWords)) (sortedUnique queries)

/-- The prover's opening under BLAKE2s-256. -/
def merkleOpen (leafWords : ℕ) {k : ℕ} (rows : Vector (List K) (2 ^ k)) (queries : List ℕ) :
    PrunedMerklePaths :=
  merkleOpenWith blake2sBytes leafWords rows queries

/-! ## The query model -/

/-- The node hash as a VCVio query model: a node queries its children's 64 bytes, left first,
with no address, on the byte-string oracle the leaves are hashed on. -/
def nodeModel : MerkleTreeExtractability.NodeQueryModel (List UInt8) Unit Digest :=
  MerkleTree.nodeQueryModelOfEncoding digestBytes digestOfBytes 32 length_digestBytes
    digestOfBytes_digestBytes

theorem nodeModel_mkQuery (left right : Digest) :
    nodeModel.mkQuery () (left, right) = nodeBytes left right := rfl

/-! ## The sorted distinct positions -/

theorem mem_sortedUnique {queries : List ℕ} {q : ℕ} : q ∈ sortedUnique queries ↔ q ∈ queries := by
  simp [sortedUnique, List.mem_dedup]

theorem pairwise_sortedUnique (queries : List ℕ) : (sortedUnique queries).Pairwise (· < ·) := by
  have hle : (sortedUnique queries).Pairwise (· ≤ ·) :=
    ((List.pairwise_mergeSort (le := fun a b ↦ decide (a ≤ b))
      (fun _ _ _ h₁ h₂ ↦ by simp only [decide_eq_true_eq] at *; omega)
      (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) queries).sublist
      (List.dedup_sublist _)).imp fun h ↦ by simpa using h
  exact (hle.and (List.nodup_dedup _)).imp fun h ↦ lt_of_le_of_ne h.1 h.2

theorem sortedUnique_eq_nil {queries : List ℕ} : sortedUnique queries = [] ↔ queries = [] := by
  rw [sortedUnique, List.dedup_eq_nil, ← List.length_eq_zero_iff, List.length_mergeSort,
    List.length_eq_zero_iff]

/-! ## The check in `Id` -/

section RunId

variable (H : List UInt8 → Digest)

private theorem run_hashRowsWith (rowWords leafWords : ℕ) :
    ∀ rows : List (List K), Id.run (hashRowsWith (m := Id) H rowWords leafWords rows) =
      if ∀ row ∈ rows, row.length = rowWords then some (rows.map (leafDigest H leafWords))
      else none
  | [] => by simp [hashRowsWith]
  | row :: rest => by
    rw [hashRowsWith]
    by_cases hw : row.length = rowWords
    · simp only [hw, ↓reduceIte, Id.run_bind, Id.run_pure]
      rw [run_hashRowsWith rowWords leafWords rest]
      by_cases hr : ∀ row ∈ rest, row.length = rowWords
      · have hc : ∀ r ∈ row :: rest, r.length = rowWords := by
          intro r hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          exacts [hw, hr r hr']
        rw [ite_eq_left hr, ite_eq_left hc]
        rfl
      · have hc : ¬ ∀ r ∈ row :: rest, r.length = rowWords :=
          fun h ↦ hr fun r hr ↦ h r (List.mem_cons_of_mem _ hr)
        rw [ite_eq_right hr, ite_eq_right hc]
        rfl
    · simp [hw]

/-- The check in `Id`: the rows in query order exactly when the stored rows have the announced
shape, the queries lie in the tree, and the walk over the octopus reaches `root`. -/
theorem run_merkleVerifyWith (root : Digest) (depth rowWords leafWords : ℕ) (queries : List ℕ)
    (paths : PrunedMerklePaths) :
    Id.run (merkleVerifyWith (m := Id) H root depth rowWords leafWords queries paths) =
      if paths.leafData.length = (sortedUnique queries).length ∧ rowWords ≤ leafWords ∧
          (∀ row ∈ paths.leafData, row.length = rowWords) ∧
          (∀ p ∈ sortedUnique queries, p < 2 ^ depth) ∧
          Id.run (MerkleTree.octopusRoot (m := Id) (fun l r ↦ H (nodeBytes l r)) depth
            ((sortedUnique queries).zip (paths.leafData.map (leafDigest H leafWords)))
            paths.siblingHashes) = some root then
        some (rowsInQueryOrder leafWords queries paths.leafData)
      else none := by
  simp only [merkleVerifyWith]
  by_cases h1 : (sortedUnique queries).length ≠ paths.leafData.length ∨ leafWords < rowWords
  · have hc : ¬ (paths.leafData.length = (sortedUnique queries).length ∧ rowWords ≤ leafWords ∧
        (∀ row ∈ paths.leafData, row.length = rowWords) ∧
        (∀ p ∈ sortedUnique queries, p < 2 ^ depth) ∧
        Id.run (MerkleTree.octopusRoot (m := Id) (fun l r ↦ H (nodeBytes l r)) depth
          ((sortedUnique queries).zip (paths.leafData.map (leafDigest H leafWords)))
          paths.siblingHashes) = some root) := fun h ↦ by omega
    simp only [h1, hc, ↓reduceIte]
    rfl
  · simp only [h1, ↓reduceIte, Id.run_bind]
    rw [run_hashRowsWith]
    have h1' : paths.leafData.length = (sortedUnique queries).length ∧ rowWords ≤ leafWords := by
      omega
    by_cases hw : ∀ row ∈ paths.leafData, row.length = rowWords
    · rw [ite_eq_left hw]
      dsimp only
      by_cases hr : ∃ p ∈ sortedUnique queries, 2 ^ depth ≤ p
      · have hr' : ¬ ∀ p ∈ sortedUnique queries, p < 2 ^ depth := fun h ↦ by
          obtain ⟨p, hp, hle⟩ := hr
          exact absurd (h p hp) (by omega)
        rw [ite_eq_left hr, ite_eq_right (fun h ↦ hr' h.2.2.2.1)]
        rfl
      · have hr' : ∀ p ∈ sortedUnique queries, p < 2 ^ depth := fun p hp ↦ by
          by_contra h
          exact hr ⟨p, hp, by omega⟩
        rw [ite_eq_right hr, Id.run_bind]
        rcases ho : Id.run (MerkleTree.octopusRoot (m := Id) (fun l r ↦ H (nodeBytes l r)) depth
          ((sortedUnique queries).zip (paths.leafData.map (leafDigest H leafWords)))
          paths.siblingHashes) with _ | r
        · rw [ite_eq_right (fun h ↦ by cases h.2.2.2.2)]
          rfl
        · by_cases hroot : r = root
          · subst hroot
            rw [ite_eq_left ⟨h1'.1, h1'.2, hw, hr', rfl⟩]
            dsimp only
            exact ite_eq_left (@decide_eq_true _ (Digest.decEq r r) rfl)
          · rw [ite_eq_right (fun h ↦ hroot (Option.some.inj h.2.2.2.2))]
            dsimp only
            exact ite_eq_right (fun h ↦ hroot (@of_decide_eq_true _ (Digest.decEq r root) h))
    · rw [ite_eq_right hw, ite_eq_right (fun h ↦ hw h.2.2.1)]
      rfl

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
  have key := MerkleTree.octopusRoot_eq_some_iff (fun l r ↦ H (nodeBytes l r)) depth
    (sortedUnique queries) (paths.leafData.map (leafDigest H leafWords)) paths.siblingHashes root
  rw [run_merkleVerifyWith]
  by_cases hc : paths.leafData.length = (sortedUnique queries).length ∧ rowWords ≤ leafWords ∧
      (∀ row ∈ paths.leafData, row.length = rowWords) ∧
      (∀ p ∈ sortedUnique queries, p < 2 ^ depth) ∧
      Id.run (MerkleTree.octopusRoot (m := Id) (fun l r ↦ H (nodeBytes l r)) depth
        ((sortedUnique queries).zip (paths.leafData.map (leafDigest H leafWords)))
        paths.siblingHashes) = some root
  · rw [ite_eq_left hc, Option.some.injEq]
    constructor
    · rintro rfl
      refine ⟨⟨hc.1, hc.2.1, hc.2.2.1, rfl⟩, key.mpr ⟨⟨pairwise_sortedUnique _, hc.2.2.2.1, ?_⟩,
        hc.2.2.2.2⟩⟩
      rw [List.length_map, hc.1]
    · rintro ⟨⟨_, _, _, rfl⟩, _⟩
      rfl
  · rw [ite_eq_right hc]
    constructor
    · intro h
      cases h
    · rintro ⟨⟨h1, h2, h3, _⟩, ho⟩
      obtain ⟨⟨_, h4, _⟩, h5⟩ := key.mp ho
      exact absurd ⟨h1, h2, h3, h4, h5⟩ hc

private theorem nodesAt_map {k : ℕ} (rows : Vector (List K) (2 ^ k)) (f : List K → Digest) :
    ∀ ps : List ℕ, (∀ p ∈ ps, p < 2 ^ k) →
      MerkleTree.nodesAt (rows.map f) ps = ps.zip ((ps.map fun q ↦ rows[q]?.getD []).map f)
  | [], _ => rfl
  | p :: ps, h => by
    have hp := h p (by simp)
    rw [MerkleTree.nodesAt_cons _ (by simpa using hp), nodesAt_map rows f ps
      (fun q hq ↦ h q (List.mem_cons_of_mem _ hq))]
    simp [hp]

/-- Completeness: the prover's opening of the tree over `rows`, each `rowWords ≤ leafWords`
wide, at nonempty queries in the tree is accepted under the tree's root, with the queried rows'
leaf images in query order. -/
theorem merkleVerifyWith_merkleOpenWith {k rowWords leafWords : ℕ}
    (rows : Vector (List K) (2 ^ k)) (queries : List ℕ) (hrw : rowWords ≤ leafWords)
    (hw : ∀ row ∈ rows.toList, row.length = rowWords) (hne : queries ≠ [])
    (hlt : ∀ q ∈ queries, q < 2 ^ k) :
    Id.run (merkleVerifyWith (m := Id) H (merkleRootWith H (rows.map (leafImage leafWords))) k
        rowWords leafWords queries (merkleOpenWith H leafWords rows queries)) =
      some (queries.map fun q ↦ leafImage leafWords (rows[q]?.getD [])) := by
  have hslt : ∀ p ∈ sortedUnique queries, p < 2 ^ k := fun p hp ↦ hlt p (mem_sortedUnique.mp hp)
  have hsne : sortedUnique queries ≠ [] := fun h ↦ hne (sortedUnique_eq_nil.mp h)
  have hroot : merkleRootWith H (rows.map (leafImage leafWords)) =
      MerkleTree.rootOfLevel (fun l r ↦ H (nodeBytes l r)) k
        (rows.map (leafDigest H leafWords)) := by
    simp only [merkleRootWith, MerkleTree.root, Vector.map_map]
    rfl
  have hoct := MerkleTree.octopusRoot_openSiblings (fun l r ↦ H (nodeBytes l r))
    (rows.map (leafDigest H leafWords)) (sortedUnique queries) hsne hslt
  rw [nodesAt_map rows _ _ hslt] at hoct
  rw [run_merkleVerifyWith, ite_eq_left]
  · congr 1
    unfold rowsInQueryOrder merkleOpenWith
    refine List.map_congr_left fun q hq ↦ ?_
    have hmem : q ∈ sortedUnique queries := mem_sortedUnique.mpr hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem), List.getElem_idxOf]
    rfl
  · refine ⟨by simp [merkleOpenWith], hrw, ?_, hslt, by rw [hroot]; exact hoct⟩
    intro row hrow
    simp only [merkleOpenWith, List.mem_map] at hrow
    obtain ⟨q, hq, rfl⟩ := hrow
    have := hslt q hq
    rw [Vector.getElem?_eq_getElem this, Option.getD_some]
    exact hw _ (by simp)

end RunId

end
end LeanerVM.Protocol
