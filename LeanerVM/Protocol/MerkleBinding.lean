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

/-- The little-endian words of a byte string, four bytes each, a trailing partial word dropped;
it inverts `List.flatMap wordBytes`. -/
def leWords : List UInt8 → List UInt32
  | b0 :: b1 :: b2 :: b3 :: rest => leWord b0 b1 b2 b3 :: leWords rest
  | _ => []

private theorem length_leWords : ∀ q : List UInt8, (leWords q).length = q.length / 4
  | _ :: _ :: _ :: _ :: rest => by
    simp only [leWords, List.length_cons, length_leWords rest]
    omega
  | [] | [_] | [_, _] | [_, _, _] => by simp only [leWords, List.length_nil, List.length_cons]

private theorem leWords_flatMap_wordBytes :
    ∀ ws : List UInt32, leWords (ws.flatMap wordBytes) = ws
  | [] => rfl
  | w :: ws => by
    simp only [List.flatMap_cons, wordBytes, List.cons_append, List.nil_append, leWords,
      leWord_wordBytes, leWords_flatMap_wordBytes ws]

/-- A query read as a node: a 64-byte input as its two 32-byte halves, left first, each eight
little-endian words. -/
def nodeOfBytes? (q : List UInt8) : Option (Digest × Digest) :=
  if h : q.length = 64 then
    let w := (leWords q).toArray
    have hw : w.size = 16 := by simp [w, length_leWords, h]
    some (⟨w.extract 0 8, by simp [hw]⟩, ⟨w.extract 8 16, by simp [hw]⟩)
  else none

/-- A node query is read back as its two children. -/
theorem nodeOfBytes?_nodeBytes (left right : Digest) :
    nodeOfBytes? (nodeBytes left right) = some (left, right) := by
  have hb : nodeBytes left right = (left.toList ++ right.toList).flatMap wordBytes := by
    rw [nodeBytes, digestBytes, digestBytes, List.flatMap_append]
  have hlen : (nodeBytes left right).length = 64 := by
    simp [nodeBytes, length_digestBytes]
  rw [hb] at hlen ⊢
  simp only [nodeOfBytes?, hlen, ↓reduceDIte, leWords_flatMap_wordBytes]
  simp [Vector.ext_iff]

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
`q`: the words of `q` after a prefix of `8 * (leafWords - rowWords)` zero bytes, or `none` if `q`
is not such a leaf (another length, or a nonzero byte in the prefix). A row wider than the leaf
is its own image, as in `leafImage`; the check rejects that width. The length is checked first,
so a query of another length is skipped without decoding. -/
def leafRow? (rowWords leafWords : ℕ) (q : List UInt8) : Option (List K) :=
  let pad := 8 * (leafWords - rowWords)
  if q.length = pad + 8 * rowWords ∧ (q.take pad).all (· == 0) then
    some (wordsOfBytes (q.drop pad))
  else none

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
    simp only [leafBytes, List.flatMap_cons, kBytes, wordBytes, List.cons_append, List.nil_append,
      wordsOfBytes, kOfBytes, leWord_wordBytes, ofWords_lowWord_highWord]
    exact congrArg _ (wordsOfBytes_leafBytes words)

/-- A leaf of `n` words has `8n` bytes. -/
theorem length_leafBytes (words : List K) : (leafBytes words).length = 8 * words.length := by
  simp [leafBytes, List.length_flatMap, kBytes, wordBytes, Nat.mul_comm]

/-- A row of `rowWords` words is read back from its leaf's bytes. -/
theorem leafRow?_leafBytes {rowWords leafWords : ℕ} {row : List K}
    (hrow : row.length = rowWords) :
    leafRow? rowWords leafWords (leafBytes (leafImage leafWords row)) = some row := by
  have hpad : (leafBytes (List.replicate (leafWords - rowWords) 0)).length =
      8 * (leafWords - rowWords) := by
    rw [length_leafBytes, List.length_replicate]
  have hzero : (leafBytes (List.replicate (leafWords - rowWords) 0)).all (· == 0) := by
    rw [leafBytes, List.all_flatMap, List.all_replicate]
    split <;> rfl
  rw [leafImage, hrow, leafBytes, List.flatMap_append, ← leafBytes, ← leafBytes]
  simp only [leafRow?, List.length_append, hpad, length_leafBytes, hrow, List.take_left' hpad,
    List.drop_left' hpad, hzero, wordsOfBytes_leafBytes, and_self, ↓reduceIte]

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
  | [], _, h => by
    cases h
    exact .nil
  | row :: rest, _, h => by
    unfold hashRowsWith at h
    split at h
    · next hwidth =>
      obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_ | ds', hds', h⟩ := Option.bind_eq_some_iff.mp h
      · cases h
      cases h
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
  obtain ⟨_ | leaves, hres, h⟩ := Option.bind_eq_some_iff.mp h
  · cases h
  dsimp only at h
  split at h
  · cases h
  next h2 =>
  obtain ⟨_ | r, hres', h⟩ := Option.bind_eq_some_iff.mp h
  · cases h
  dsimp only at h
  split at h
  · next hr =>
    cases h
    obtain rfl : r = root := @of_decide_eq_true _ (Digest.decEq r root) hr
    exact ⟨leaves, by omega, by omega, hashRowsWith_eq_some hres,
      fun p hp ↦ Nat.lt_of_not_le fun hge ↦ h2 ⟨p, hp, hge⟩, hres', rfl⟩
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
