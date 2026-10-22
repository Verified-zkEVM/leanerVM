/-
  LeanerVM.Protocol.MerkleBinding

  The rows a log of byte-hash queries commits to, read off it, and the binding of leanVM's
  pruned openings by replaying the log: an accepted opening yields the rows read off the
  adversary's part of the log, unless the log shows a collision, an input with two answers, or
  a fresh answer equal to a digest already known.
-/

module

public import LeanerVM.Protocol.Merkle
public import LeanerVM.Protocol.ToVCVio.MerkleLog

/-!
# Binding of leanVM's Merkle openings by log replay

The parsers are Category B, transcribed; `binding_of_log` is a statement about the verifier,
written from the specification. leanVM's leaves and nodes are hashed on one byte-string oracle
with no tag (`fiat_shamir/src/merkle.rs:38-67` at `a386121f84292f6fa663aaa3e570c15bc0240ea2`): a
node is the
hash of its children's 64 bytes (`nodeBytes`), a leaf the hash of its row's leaf image as bytes
(`leafBytes ∘ leafImage`). A query parses as a node when it has 64 bytes (`nodeOfBytes?`), and as
the leaf of a row of `rowWords` words in leaves of `leafWords` when it is that row's leaf image
as bytes (`leafRow?`); a 64-byte leaf parses as both, which the generic theory allows.

`extractRows log root depth rowWords leafWords p` is the row at position `p` of the tree under
`root`, read top-down off `log` by `MerkleTree.extractLeaf`: `none` when the log does not reach
the position, or when the leaf query found there is not the leaf image of a row of `rowWords`
words (wrong length, or a nonzero word in the zero prefix).

`binding_of_log` specialises `MerkleTree.binding_of_log` to `merkleVerifyWith` run with every
hash answered from the log: every row the check returns is the leaf image of the row extracted
from the adversary's log at its query, under the hypotheses of the generic theorem, with the
digests known from that log being the roots and the two 32-byte halves of each of its 64-byte
inputs. `extractRows_determined` specialises `MerkleTree.extractLeaf_determined`: under the same
hypotheses but the collision, the rows read off a log are those read off its earlier part.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash MerkleTree
open MerkleTreeExtractor (QueryLog)

@[expose] public section

/-! ## Parsing queries -/

/-- A query read as a node: a 64-byte input as its two 32-byte halves, left first. -/
def nodeOfBytes? (q : List UInt8) : Option (Digest × Digest) :=
  if q.length = 64 then some (digestOfBytes (q.take 32), digestOfBytes (q.drop 32)) else none

/-- A node query is read back as its two children. -/
theorem nodeOfBytes?_nodeBytes (left right : Digest) :
    nodeOfBytes? (nodeBytes left right) = some (left, right) := by
  have hl := length_digestBytes left
  have hr := length_digestBytes right
  simp only [nodeOfBytes?, nodeBytes, List.length_append, hl, hr, ↓reduceIte]
  rw [← hl, List.take_left, List.drop_left, digestOfBytes_digestBytes, digestOfBytes_digestBytes]

/-- The `K` word of eight little-endian bytes. -/
def kOfBytes (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : K :=
  ofWords (leWord b0 b1 b2 b3) (leWord b4 b5 b6 b7)

/-- The words of a byte string, eight little-endian bytes each, a trailing partial word dropped;
it inverts `leafBytes` (`wordsOfBytes_leafBytes`). -/
def wordsOfBytes : List UInt8 → List K
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    kOfBytes b0 b1 b2 b3 b4 b5 b6 b7 :: wordsOfBytes rest
  | _ => []

/-- The row of `rowWords` words whose leaf image in leaves of `leafWords` words has the bytes
`q`: the words of `q` after the zero prefix, or `none` if `q` is not such a leaf. A row wider
than the leaf is its own image, as in `leafImage`; the check rejects that width. The length is
checked first, so a query of another length is skipped without decoding. -/
def leafRow? (rowWords leafWords : ℕ) (q : List UInt8) : Option (List K) :=
  if q.length ≠ 8 * (leafWords - rowWords + rowWords) then none
  else
    let row := (wordsOfBytes q).drop (leafWords - rowWords)
    if row.length = rowWords ∧ leafBytes (leafImage leafWords row) = q then some row else none

/-- Splitting a `K` word into its two words and joining them again is the identity. -/
private theorem ofWords_lowWord_highWord (a : K) : ofWords (lowWord a) (highWord a) = a := by
  apply BF64.toBitVec_injective
  have := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := a.toBitVec) (start₁ := 0)
    (len₁ := 32) (start₂ := 32) (len₂ := 32) rfl
  simpa [ofWords, lowWord, highWord] using this

/-- The words of a leaf are read back from its bytes. -/
theorem wordsOfBytes_leafBytes : ∀ words : List K, wordsOfBytes (leafBytes words) = words
  | [] => rfl
  | a :: words => by
    have h : leafBytes (a :: words) = kBytes a ++ leafBytes words := by
      simp [leafBytes, List.flatMap_cons]
    rw [h]
    simp only [kBytes, wordBytes, List.cons_append, List.nil_append, wordsOfBytes, kOfBytes,
      leWord_wordBytes, ofWords_lowWord_highWord, wordsOfBytes_leafBytes words]

/-- A leaf of `n` words has `8n` bytes. -/
theorem length_leafBytes : ∀ words : List K, (leafBytes words).length = 8 * words.length
  | [] => rfl
  | a :: words => by
    have h : leafBytes (a :: words) = kBytes a ++ leafBytes words := by
      simp [leafBytes, List.flatMap_cons]
    rw [h, List.length_append, length_leafBytes words, List.length_cons]
    simp only [kBytes, wordBytes, List.length_append, List.length_cons, List.length_nil]
    omega

/-- A row of `rowWords` words is read back from its leaf's bytes. -/
theorem leafRow?_leafBytes {rowWords leafWords : ℕ} {row : List K}
    (hrow : row.length = rowWords) :
    leafRow? rowWords leafWords (leafBytes (leafImage leafWords row)) = some row := by
  have hdrop : (leafImage leafWords row).drop (leafWords - rowWords) = row := by
    rw [leafImage, hrow, List.drop_left' (List.length_replicate ..)]
  have hlen : (leafBytes (leafImage leafWords row)).length =
      8 * (leafWords - rowWords + rowWords) := by
    rw [length_leafBytes, leafImage, List.length_append, List.length_replicate, hrow]
  simp only [leafRow?, hlen, ne_eq, not_true_eq_false, ↓reduceIte, wordsOfBytes_leafBytes, hdrop,
    hrow, and_self]

/-! ## The rows read off a log -/

/-- The row at position `p` of the tree of depth `depth` under `root`, rows of `rowWords` words
in leaves of `leafWords`, read top-down off `log`. -/
def extractRows (log : QueryLog (List UInt8) Digest) (root : Digest)
    (depth rowWords leafWords p : ℕ) : Option (List K) :=
  @extractLeaf _ _ _ Digest.decEq nodeOfBytes? (leafRow? rowWords leafWords) log root depth p

/-- `Digest` hashed through its word list, for the one-pass extraction. -/
@[instance_reducible] def Digest.hashable : Hashable Digest := ⟨fun d ↦ hash d.toList⟩

/-- The rows at all `2^depth` positions, in position order, read off `log` in one pass. -/
def extractAllRows (log : QueryLog (List UInt8) Digest) (root : Digest)
    (depth rowWords leafWords : ℕ) : List (Option (List K)) :=
  @extractLeaves _ _ _ Digest.decEq Digest.hashable nodeOfBytes? (leafRow? rowWords leafWords) log
    root depth

/-- The one-pass extraction is `extractRows` at every position. -/
theorem extractAllRows_eq (log : QueryLog (List UInt8) Digest) (root : Digest)
    (depth rowWords leafWords : ℕ) :
    extractAllRows log root depth rowWords leafWords =
      (List.range (2 ^ depth)).map (extractRows log root depth rowWords leafWords) :=
  @extractLeaves_eq _ _ _ Digest.decEq Digest.hashable _ _ _ _ _

/-! ## The check in `Option` -/

private theorem hashRowsWith_eq_some {ans : List UInt8 → Option Digest} {rowWords leafWords : ℕ} :
    ∀ {rows : List (List K)} {ds : List Digest},
      hashRowsWith ans rowWords leafWords rows = some (some ds) →
      List.Forall₂ (fun row d ↦ row.length = rowWords ∧
        ans (leafBytes (leafImage leafWords row)) = some d) rows ds
  | [], ds, h => by
    simp only [hashRowsWith, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | row :: rest, ds, h => by
    unfold hashRowsWith at h
    split at h
    · next hwidth =>
      simp only [Option.bind_eq_bind, Option.pure_def] at h
      obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ds', hds', h⟩ := Option.bind_eq_some_iff.mp h
      rcases ds' with _ | ds'
      · cases h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact .cons ⟨hwidth, hd⟩ (hashRowsWith_eq_some hds')
    · cases h

/-- The check with every hash answered by a partial oracle `ans`, when it accepts with `rows`:
the conditions of `PrunedMerklePaths.Accepts`, every leaf digest and node an answer of `ans`. -/
theorem merkleVerifyWith_option_eq_some {ans : List UInt8 → Option Digest} {root : Digest}
    {depth rowWords leafWords : ℕ} {queries : List ℕ} {paths : PrunedMerklePaths}
    {rows : List (List K)}
    (h : merkleVerifyWith (m := Option) ans root depth rowWords leafWords queries paths =
      some (some rows)) :
    ∃ leaves, paths.leafData.length = (sortedUnique queries).length ∧ rowWords ≤ leafWords ∧
      List.Forall₂ (fun row d ↦ row.length = rowWords ∧
        ans (leafBytes (leafImage leafWords row)) = some d) paths.leafData leaves ∧
      (∀ p ∈ sortedUnique queries, p < 2 ^ depth) ∧
      prunedRoot (fun l r ↦ ans (nodeBytes l r)) depth ((sortedUnique queries).zip leaves)
        paths.siblingHashes = some (some root) ∧
      rows = rowsInQueryOrder leafWords queries paths.leafData := by
  unfold merkleVerifyWith at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  split at h
  · cases h
  next h1 =>
  obtain ⟨res, hres, h⟩ := Option.bind_eq_some_iff.mp h
  rcases res with _ | leaves
  · cases h
  dsimp only at h
  split at h
  · cases h
  next h2 =>
  obtain ⟨res', hres', h⟩ := Option.bind_eq_some_iff.mp h
  rcases res' with _ | r
  · cases h
  dsimp only at h
  split at h
  · next hr =>
    cases h
    have hr' : r = root := @of_decide_eq_true _ (Digest.decEq r root) hr
    subst hr'
    refine ⟨leaves, by omega, by omega, hashRowsWith_eq_some hres, fun p hp ↦ ?_, hres', rfl⟩
    by_contra hge
    exact h2 ⟨p, hp, by omega⟩
  · cases h

/-! ## Binding -/

/-- Binding by log replay for leanVM's pruned openings. If the check of a phase's opening under
`root ∈ roots`, run with every hash answered by `ans` from the log `logA ++ logV`, accepts with
`rows`, and the log is consistent, has no collision and no fresh hit with respect to `logA` and
the roots, then a row is read off `logA` at every query, and the returned rows, in query order,
are their leaf images. -/
theorem binding_of_log (logA logV : QueryLog (List UInt8) Digest)
    (ans : List UInt8 → Option Digest) (hans : ∀ q d, ans q = some d → ⟨q, d⟩ ∈ logA ++ logV)
    (roots : List Digest) (root : Digest) (hroot : root ∈ roots) (depth rowWords leafWords : ℕ)
    (queries : List ℕ) (paths : PrunedMerklePaths) (rows : List (List K))
    (hV : merkleVerifyWith (m := Option) ans root depth rowWords leafWords queries paths =
      some (some rows))
    (hcons : Consistent (logA ++ logV)) (hcoll : ¬ HasCollision (logA ++ logV))
    (hhit : ¬ FreshHit nodeOfBytes? roots logA logV) :
    queries.map (fun q ↦ (extractRows logA root depth rowWords leafWords q).map
      (leafImage leafWords)) = rows.map some := by
  obtain ⟨leaves, hlen, -, hrows, hlt, hwalk, rfl⟩ := merkleVerifyWith_option_eq_some hV
  have hstored := @MerkleTree.binding_of_log _ _ _ Digest.decEq nodeOfBytes? nodeBytes
    nodeOfBytes?_nodeBytes (leafRow? rowWords leafWords) logA logV ans hans roots root hroot depth
    (sortedUnique queries) paths.leafData leaves paths.siblingHashes hlen.symm
    (pairwise_sortedUnique queries) hlt
    (hrows.imp fun _ _ hr ↦ ⟨_, leafRow?_leafBytes hr.1, hr.2⟩) hwalk hcons hcoll hhit
  unfold rowsInQueryOrder
  rw [List.map_map]
  refine List.map_congr_left fun q hq ↦ ?_
  have hmem : q ∈ sortedUnique queries := mem_sortedUnique.mpr hq
  have hi := List.idxOf_lt_length_of_mem hmem
  have := congrArg (·[(sortedUnique queries).idxOf q]?) hstored
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (hlen ▸ hi), Option.map_some, List.getElem_idxOf,
    Option.some.injEq] at this
  simp only [Function.comp_apply, extractRows, this, Option.map_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hi), Option.getD_some]

/-- The rows read off a log are those read off `logA`, its part up to a point, when the log is
consistent and has no fresh hit with respect to `logA` and roots containing `root`. -/
theorem extractRows_determined (logA logV : QueryLog (List UInt8) Digest) (roots : List Digest)
    (root : Digest) (hroot : root ∈ roots) (hcons : Consistent (logA ++ logV))
    (hhit : ¬ FreshHit nodeOfBytes? roots logA logV) (depth rowWords leafWords p : ℕ) :
    extractRows (logA ++ logV) root depth rowWords leafWords p =
      extractRows logA root depth rowWords leafWords p :=
  @extractLeaf_determined _ _ _ Digest.decEq nodeOfBytes? (leafRow? rowWords leafWords) logA logV
    roots root hroot hcons hhit depth p

end
end LeanerVM.Protocol
