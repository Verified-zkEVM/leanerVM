import LeanerVM.Protocol.MerkleBinding
import LeanerVM.Protocol.Transcript

/-!
# Merkle binding by log replay tests

First a toy tree over a one-byte hash on byte lists, where leaves and nodes are both two-byte
queries, so that every leaf also parses as a node. `leafPreimage` returns the first of two leaf
queries answered by one digest, and nothing for a digest that only a non-leaf query answers. An
honest opening meets every hypothesis of `MerkleTree.binding_of_log` and opens the extracted
leaf. Then one mutation per hypothesis on the log, and one for the sorted positions: in each the
check accepts a payload other than the one extracted, or with none extracted, and exactly the
targeted hypothesis fails;
with the fresh hit, the leaf is read off the whole log but not off the adversary's part.

Then leanVM's trees under BLAKE2s: the leaf parse, the node parse (the seed's 78-byte preimage is
no node), the rows read off the honest prover's log of
the eight-leaf tree of the pinned leanVM's tests (`fiat_shamir/src/merkle.rs:283-351`), with and
without a zero prefix, a log missing one leaf query, and the hypotheses of `binding_of_log` on the
log of the check of the Rust's octopus.
-/

namespace LeanerVMTests.Protocol.MerkleBinding

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.MerkleTree
open MerkleTreeExtractor (QueryLog)

/-! ## A toy tree -/

/-- A one-byte hash on byte lists. -/
def toyHash (b : List UInt8) : UInt8 := b.foldl (fun a x ↦ (a ^^^ x) * 167 + 101) 7

abbrev ToyLog := QueryLog (List UInt8) UInt8

/-- The log of the toy hash on some queries. -/
def logOf (qs : List (List UInt8)) : ToyLog := qs.map fun q ↦ ⟨q, toyHash q⟩

/-- A node is the query on its two children. -/
def toyNode (l r : UInt8) : List UInt8 := [l, r]

def toyNode? : List UInt8 → Option (UInt8 × UInt8)
  | [l, r] => some (l, r)
  | _ => none

/-- A leaf is a two-byte payload queried as itself: every leaf parses as a node too. -/
def toyLeaf? (q : List UInt8) : Option (List UInt8) := if q.length = 2 then some q else none

theorem toyNode?_toyNode (l r : UInt8) : toyNode? (toyNode l r) = some (l, r) := rfl

/-- The toy check of an opening, every hash answered from the log `logV`: the payloads hashed,
then the walk over the siblings, which must reach `root`. -/
def toyAccepts (logV : ToyLog) (root : UInt8) (depth : ℕ) (positions : List ℕ)
    (payloads : List (List UInt8)) (sibs : List UInt8) : Bool :=
  match payloads.mapM (logAnswer logV) with
  | none => false
  | some ds =>
    prunedRoot (fun l r ↦ logAnswer logV (toyNode l r)) depth (positions.zip ds) sibs ==
      some (some root)

/-- The hypotheses of `binding_of_log` on the log: consistent, no collision, no fresh hit. -/
def toyHypotheses (logA logV : ToyLog) (roots : List UInt8) : List Bool :=
  [decide (Consistent (logA ++ logV)), decide (¬ HasCollision (logA ++ logV)),
    decide (¬ FreshHit toyNode? roots logA logV)]

/-- The leaves read off `logA` at the positions. -/
def toyExtract (logA : ToyLog) (root : UInt8) (depth : ℕ) (positions : List ℕ) :
    List (Option (List UInt8)) :=
  positions.map (extractLeaf toyNode? toyLeaf? logA root depth)

def x0 : List UInt8 := [1, 2]
def x1 : List UInt8 := [3, 4]
def d0 : UInt8 := toyHash x0
def d1 : UInt8 := toyHash x1
def toyRoot : UInt8 := toyHash (toyNode d0 d1)

/-- The honest prover's log of the two-leaf tree over `x0, x1`. -/
def honestA : ToyLog := logOf [x0, x1, toyNode d0 d1]

/-! ### `leafPreimage` -/

/- `[0, 187]` collides with `x0`; `[9, 9, 9]` is not a leaf. -/
#guard toyHash [0, 187] = d0
#guard leafPreimage toyLeaf? (logOf [x0, [0, 187]]) d0 = some x0
#guard leafPreimage toyLeaf? (logOf [[0, 187], x0]) d0 = some [0, 187]
#guard leafPreimage toyLeaf? (logOf [x0, [9, 9, 9]]) (toyHash [9, 9, 9]) = none
#guard leafPreimage toyLeaf? (logOf [x0]) d1 = none

/-! ### The honest opening -/

/- Opened at position `0` with the sibling `d1`; the check's log is its two queries. -/
#guard toyAccepts (logOf [x0, toyNode d0 d1]) toyRoot 1 [0] [x0] [d1]
#guard toyHypotheses honestA (logOf [x0, toyNode d0 d1]) [toyRoot] = [true, true, true]
#guard toyExtract honestA toyRoot 1 [0, 1] = [some x0, some x1]

/-- The theorem at the honest opening, every hypothesis decided: they hold together. -/
example : [0].map (extractLeaf toyNode? toyLeaf? honestA toyRoot 1) = [x0].map some :=
  MerkleTree.binding_of_log toyNode? toyNode toyNode?_toyNode toyLeaf? honestA
    (logOf [x0, toyNode d0 d1]) (logAnswer (logOf [x0, toyNode d0 d1]))
    (fun _ _ h ↦ List.mem_append_right _ (mem_of_logAnswer_eq_some h)) [toyRoot] toyRoot
    (by decide) 1 [0] [x0] [d0] [d1] rfl (by decide) (by decide)
    (.cons ⟨x0, by decide, by decide⟩ .nil) (by decide) (by decide) (by decide) (by decide)

/- The tree of depth two over four leaves, opened at `1, 2`. -/
def x2 : List UInt8 := [5, 6]
def x3 : List UInt8 := [7, 8]
def n01 : UInt8 := toyHash (toyNode d0 d1)
def n23 : UInt8 := toyHash (toyNode (toyHash x2) (toyHash x3))
def root4 : UInt8 := toyHash (toyNode n01 n23)
def honest4 : ToyLog :=
  logOf [x0, x1, x2, x3, toyNode d0 d1, toyNode (toyHash x2) (toyHash x3), toyNode n01 n23]
def check4 : ToyLog :=
  logOf [x1, x2, toyNode d0 d1, toyNode (toyHash x2) (toyHash x3), toyNode n01 n23]

#guard toyAccepts check4 root4 2 [1, 2] [x1, x2] [d0, toyHash x3]
#guard toyHypotheses honest4 check4 [root4] = [true, true, true]
#guard toyExtract honest4 root4 2 [0, 1, 2, 3] = [some x0, some x1, some x2, some x3]
#guard extractLeaves toyNode? toyLeaf? honest4 root4 2 = [some x0, some x1, some x2, some x3]

/-! ### A collision

The adversary queries `x0` and `[0, 187]`, which collide, then the tree over `x0, x1`; the check
opens `[0, 187]` at position `0`. Only the collision hypothesis fails. -/

def collA : ToyLog := logOf [x0, [0, 187], x1, toyNode d0 d1]
def collV : ToyLog := logOf [[0, 187], toyNode d0 d1]

#guard toyAccepts collV toyRoot 1 [0] [[0, 187]] [d1]
#guard toyHypotheses collA collV [toyRoot] = [true, false, true]
#guard toyExtract collA toyRoot 1 [0] = [some x0]

/-! ### A fresh hit

The adversary queries only the root's node, on children it never derives; the check's leaf query
is fresh, and its answer `d0` is a child of that node. Only the fresh-hit hypothesis fails, and
nothing is read off the log at the leaf. -/

def hitA : ToyLog := logOf [toyNode d0 d1]
def hitV : ToyLog := logOf [x0, toyNode d0 d1]

#guard toyAccepts hitV toyRoot 1 [0] [x0] [d1]
#guard toyHypotheses hitA hitV [toyRoot] = [true, true, false]
#guard toyExtract hitA toyRoot 1 [0] = [none]

/- The leaf joins the root after the root's node is logged: read off the whole log, but not off
the adversary's part. With no fresh hit, the two agree (`extractLeaf_determined`). -/
#guard toyExtract (hitA ++ hitV) toyRoot 1 [0] = [some x0]
#guard toyExtract (honestA ++ logOf [x0, toyNode d0 d1]) toyRoot 1 [0, 1] =
  toyExtract honestA toyRoot 1 [0, 1]

/- A fresh answer equal to the root is a hit too: the adversary queries nothing. -/
#guard toyAccepts (logOf [x0, toyNode d0 d1]) toyRoot 1 [0] [x0] [d1]
#guard toyHypotheses [] (logOf [x0, toyNode d0 d1]) [toyRoot] = [true, true, false]
#guard toyExtract [] toyRoot 1 [0] = [none]

/-! ### An inconsistent log

The adversary's node query is answered by `99`; the check's answer to the same query, from its
own log, is the root. Only consistency fails, and the root has no node in the adversary's log. -/

def inconsA : ToyLog := [⟨x0, d0⟩, ⟨x1, d1⟩, ⟨toyNode d0 d1, 99⟩]
def inconsV : ToyLog := [⟨x0, d0⟩, ⟨toyNode d0 d1, toyRoot⟩]

#guard toyRoot ≠ 99 ∧ toyRoot ≠ d0 ∧ toyRoot ≠ d1 ∧ d0 ≠ d1 ∧ 99 ≠ d0 ∧ 99 ≠ d1
#guard toyAccepts inconsV toyRoot 1 [0] [x0] [d1]
#guard toyHypotheses inconsA inconsV [toyRoot] = [false, true, true]
#guard toyExtract inconsA toyRoot 1 [0] = [none]

/-! ### Unsorted positions

At positions `[1, 0]` the walk checks only the first leaf against the root: leaf `1` is honest,
and leaf `0` is a payload `y` whose parent the walk never compares. Every hypothesis on the log
holds, and the leaf read off the log at `0` is `x0`. -/

def y : List UInt8 := [42, 43]
def unsortedV : ToyLog := logOf [x1, y, toyNode d0 d1, toyNode (toyHash y) 0]

#guard toyAccepts unsortedV toyRoot 1 [1, 0] [x1, y] [d0, 0]
#guard toyHypotheses honestA unsortedV [toyRoot] = [true, true, true]
#guard toyExtract honestA toyRoot 1 [1, 0] = [some x1, some x0]

/-! ## leanVM's trees -/

/-- The word `n`. -/
def w (n : ℕ) : K := K.ofBits n

/- The leaf parse: a row is read back from its leaf image, and nothing from bytes that are not
a leaf image of a row of the announced width. -/
#guard leafRow? 3 4 (leafBytes [0, w 5, w 6, w 7]) = some [w 5, w 6, w 7]
#guard leafRow? 3 4 (leafBytes [w 1, w 5, w 6, w 7]) = none
#guard leafRow? 3 4 ((leafBytes [0, w 5, w 6, w 7]).set 3 1) = none
#guard leafRow? 3 4 (leafBytes [w 5, w 6, w 7]) = none
#guard leafRow? 4 4 (leafBytes [0, w 5, w 6, w 7]) = some [0, w 5, w 6, w 7]
#guard leafRow? 4 4 ((leafBytes [w 4, w 5, w 6, w 7]).drop 1) = none
#guard nodeOfBytes? ((List.range 64).map Nat.toUInt8) =
  some (digestOfBytes ((List.range 32).map Nat.toUInt8),
    digestOfBytes ((List.range 32).map fun i ↦ (i + 32).toUInt8))
#guard nodeOfBytes? ((List.range 63).map (·.toUInt8)) = none
-- The seed's 78-byte preimage is no node.
example (ph : Digest) : nodeOfBytes? (seedPreimageOf ph) = none := by
  simp [nodeOfBytes?, length_seedPreimageOf]

/-- The all-zero digest. -/
def zeroDigest : Digest := Vector.replicate 8 0

/-- The node queries of the tree over a level of digests, bottom-up, under BLAKE2s. -/
def nodeQueries : ℕ → List Digest → QueryLog (List UInt8) Digest
  | 0, _ => []
  | k + 1, level =>
    let qs := (List.range (level.length / 2)).map fun j ↦
      nodeBytes (level.getD (2 * j) zeroDigest) (level.getD (2 * j + 1) zeroDigest)
    qs.map (fun q ↦ ⟨q, blake2sBytes q⟩) ++ nodeQueries k (qs.map blake2sBytes)

/-- The honest prover's log of the tree over `rows`: every leaf query, then every node query,
bottom-up. -/
def honestLog (leafWords depth : ℕ) (rows : List (List K)) : QueryLog (List UInt8) Digest :=
  let leaves := rows.map fun r ↦ leafBytes (leafImage leafWords r)
  leaves.map (fun q ↦ ⟨q, blake2sBytes q⟩) ++ nodeQueries depth (leaves.map blake2sBytes)

/-- Row `q` of the eight-leaf tree of the Rust's tests: the words `4q, …, 4q + 3`. -/
def row (q : ℕ) : List K := (List.range 4).map fun j ↦ w (4 * q + j)

def rows8 : Vector (List K) (2 ^ 3) := Vector.ofFn fun q ↦ row q

def root8 : Digest :=
  #v[0x683740ce, 0x4c08ee81, 0x0c851c06, 0xa9800368, 0x28da23a1, 0x751fe579, 0x83a776d8, 0x91ed3198]

def log8 : QueryLog (List UInt8) Digest := honestLog 4 3 rows8.toList

/- Every row is read back off the honest log, in one pass and position by position. -/
#guard extractAllRows log8 root8 3 4 4 = rows8.toList.map some
#guard (List.range 8).map (extractRows log8 root8 3 4 4) = rows8.toList.map some

/- With one leaf query missing, nothing is read at its position. -/
#guard extractAllRows (log8.eraseIdx 5) root8 3 4 4 =
  (rows8.toList.map some).set 5 none

/- Rows of three words in leaves of four, each hashed as its image after one zero word. -/
def rows3 : List (List K) := (List.range 8).map fun q ↦ (row q).drop 1

#guard extractAllRows (honestLog 4 3 rows3)
  (merkleRootWith blake2sBytes (Vector.ofFn (n := 2 ^ 3) fun q ↦ leafImage 4 (rows3.getD q [])))
  3 3 4 = rows3.map some

/-- The byte hash with a log of its queries. -/
def loggedHash (b : List UInt8) : StateM (QueryLog (List UInt8) Digest) Digest := do
  let d := blake2sBytes b
  modify (· ++ [⟨b, d⟩])
  pure d

/-- The Rust's octopus at the queries `[5, 1, 5, 3, 1]`, as the prover opens it. -/
def good : PrunedMerklePaths := merkleOpen (merkleCommit 4 rows8) [5, 1, 5, 3, 1]

/-- The log of the check of the octopus: three leaf queries and six node queries. -/
def logV : QueryLog (List UInt8) Digest :=
  ((merkleVerifyWith loggedHash root8 3 4 4 [5, 1, 5, 3, 1] good).run []).run.2

/- The check answered from its own log accepts, every hypothesis of `binding_of_log` holds with
the honest prover's log as the adversary's, and the returned rows are those read off it. -/
#guard logV.length = 9
#guard merkleVerifyWith (m := Option) (logAnswer logV) root8 3 4 4 [5, 1, 5, 3, 1] good =
  some (some [row 5, row 1, row 5, row 3, row 1])
#guard decide (Consistent (log8 ++ logV)) && decide (¬ HasCollision (log8 ++ logV)) &&
  decide (¬ FreshHit nodeOfBytes? [root8] log8 logV)
#guard [5, 1, 5, 3, 1].map (fun q ↦ (extractRows log8 root8 3 4 4 q).map (leafImage 4)) =
  [some (row 5), some (row 1), some (row 5), some (row 3), some (row 1)]

/- With the adversary's log the check's own minus the leaf query of row 3, that query is fresh
and its answer a child of a logged node: a fresh hit, and nothing is read at position 3. -/
#guard decide (FreshHit nodeOfBytes? [root8] (logV.eraseIdx 1) logV)
#guard extractRows (logV.eraseIdx 1) root8 3 4 4 3 = none
#guard extractRows (logV.eraseIdx 1 ++ logV) root8 3 4 4 3 = some (row 3)

/- The honest log followed by the check's: no fresh hit, so the rows read off both agree. -/
#guard extractAllRows (log8 ++ logV) root8 3 4 4 = extractAllRows log8 root8 3 4 4

end LeanerVMTests.Protocol.MerkleBinding
