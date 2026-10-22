/-
  LeanerVM.Protocol.ToVCVio.Merkle

  Binary Merkle trees over an abstract node hash, and their pruned multi-openings in the stream
  form: the opened leaves at sorted positions and one list of sibling digests, bottom-up and left
  to right. The walk that recomputes the root from such an opening, the honest prover with
  completeness, and the reading of an opening as VCVio's path-pruned `BatchOpening`, under which
  the walk computes VCVio's putative root for every node hash. Also the `NodeQueryModel` of a
  node hash that queries the concatenated encodings of its two children. Candidate for VCVio.
-/

module

public import VCVio.CryptoFoundations.MerkleTree.ExtractionKernel
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Opening
public import ToMathlib.Data.IndexedBinaryTree.Perfect

/-!
# Merkle trees and their pruned openings

A tree over `2^k` leaves is built level by level: each parent is `hashPair` of its two children,
the left child first; `root` hashes the leaves first. Node `i` of a level has children `2i` and
`2i + 1` of the level below, so leaf `p`'s ancestor at height `h` is `p / 2^h`, and the top bit
of `p` chooses the root's child, as in VCVio's `SkeletonLeafIndex.ofNat`.

A pruned opening of the leaves at strictly increasing positions carries their values and one
list of siblings: walking up from the leaves, level by level and left to right, a node whose
sibling is also on an opened path is paired with it, and any other node takes the next supplied
sibling. `levelStep` is one level of that walk and `fold` the walk, both over a `NodeAlgebra`
that says how a parent is formed from its children: by a hash in any monad (`prunedRoot`), or
as a VCVio `BatchOpening` of the perfect subtree below the parent (`toBatchOpening`). The walk
fails when the siblings run out or are left over, and reads the first node of the top level.

`prunedRoot_eq_some_iff` is the reading: for every node hash, the walk reaches a root exactly
when `toBatchOpening` reads the opening as VCVio's and VCVio's putative root is that root.
`openSiblings` is the honest prover and `prunedRoot_openSiblings` its completeness. A prover
builds the tree once, as its `Levels` (`buildLevels`), and reads the root and the siblings of
every opening off it (`Levels.root`, `Levels.siblings`); `root_buildLevels` and
`siblings_buildLevels` equate these with `rootOfLevel` and `openSiblings`.
`nodeQueryModelOfEncoding` is the VCVio query model of a node hash on `encode left ++ encode
right`, which carries no address.
-/

namespace LeanerVM.Protocol.MerkleTree

open BinaryTree InductiveMerkleTree

@[expose] public section

variable {D : Type}

/-! ## The tree -/

section Tree

variable (hashPair : D → D → D)

/-- The parents of a level of `2^(k+1)` nodes: adjacent pairs hashed, the left child first. -/
def parents {k : ℕ} (level : Vector D (2 ^ (k + 1))) : Vector D (2 ^ k) :=
  Vector.ofFn fun j ↦
    hashPair (level[2 * j.val]'(by have := j.isLt; rw [Nat.pow_succ]; omega))
      (level[2 * j.val + 1]'(by have := j.isLt; rw [Nat.pow_succ]; omega))

/-- The root of a level of `2^k` digests. -/
def rootOfLevel : (k : ℕ) → Vector D (2 ^ k) → D
  | 0, level => level[0]
  | k + 1, level => rootOfLevel k (parents hashPair level)

/-- The root of `2^k` leaves, each hashed by `hashLeaf`. -/
def root {L : Type} (hashLeaf : L → D) {k : ℕ} (leaves : Vector L (2 ^ k)) : D :=
  rootOfLevel hashPair k (leaves.map hashLeaf)

end Tree

/-! ## The walk over a pruned opening -/

/-- How the walk forms a parent at height `h + 1` from its children at height `h`, in a monad
`m`: from two opened children, from an opened left child and a supplied right sibling, or from a
supplied left sibling and an opened right child. `T h` is what the walk carries for a node at
height `h`. -/
structure NodeAlgebra (m : Type → Type) (D : Type) (T : ℕ → Type) where
  both : {h : ℕ} → T h → T h → m (T (h + 1))
  withRight : {h : ℕ} → T h → D → m (T (h + 1))
  withLeft : {h : ℕ} → D → T h → m (T (h + 1))

/-- The node algebra of a node hash: every parent is the hash of its two children. -/
def NodeAlgebra.ofHash {m : Type → Type} (hash : D → D → m D) : NodeAlgebra m D fun _ ↦ D where
  both a b := hash a b
  withRight a s := hash a s
  withLeft s b := hash s b

variable {m : Type → Type} [Monad m] {T : ℕ → Type}

/-- The parent of node `i` and a supplied sibling: the sibling on the right of an even node, on
the left of an odd one. -/
def withSupplied (A : NodeAlgebra m D T) {h : ℕ} (i : ℕ) (a : T h) (s : D) : m (T (h + 1)) :=
  if i % 2 = 0 then A.withRight a s else A.withLeft s a

/-- Prepend the parent at index `i`, formed first, to the rest of a level's result. -/
def consParent {U : Type} (i : ℕ) (parent : m U) (rest : m (Option (List (ℕ × U) × List D))) :
    m (Option (List (ℕ × U) × List D)) := do
  let p ← parent
  let r ← rest
  pure (r.map fun x ↦ ((i, p) :: x.1, x.2))

/-- Continue with the next supplied sibling and the rest, or fail if none is left. -/
def withNext {X : Type} (sibs : List D) (k : D → List D → m (Option X)) : m (Option X) :=
  match sibs with
  | [] => pure none
  | s :: rest => k s rest

/-- One level of the walk: the opened nodes of a level, sorted by index, folded into their
parents at half the index. Node `i` is paired with the next node when `i` is even and the next
is `i + 1`; otherwise it takes the next supplied sibling, and the level fails if none is left.
Returns the parents and the siblings left. -/
def levelStep (A : NodeAlgebra m D T) {h : ℕ} :
    List (ℕ × T h) → List D → m (Option (List (ℕ × T (h + 1)) × List D))
  | [], sibs => pure (some ([], sibs))
  | (i, a) :: tl, sibs =>
    match tl with
    | (j, b) :: rest =>
      if i % 2 = 0 ∧ j = i + 1 then consParent (i / 2) (A.both a b) (levelStep A rest sibs)
      else withNext sibs fun s sibs ↦
        consParent (i / 2) (withSupplied A i a s) (levelStep A ((j, b) :: rest) sibs)
    | [] => withNext sibs fun s sibs ↦
        consParent (i / 2) (withSupplied A i a s) (pure (some ([], sibs)))
termination_by structural nodes => nodes

/-- The walk over `k` levels from height `h` to height `t = h + k`: the first node of the top
level, or `none` if a level runs out of siblings or siblings are left over. -/
def fold (A : NodeAlgebra m D T) :
    (k h t : ℕ) → h + k = t → List (ℕ × T h) → List D → m (Option (T t))
  | 0, _, _, rfl, nodes, sibs =>
    pure (match nodes, sibs with
      | (_, a) :: _, [] => some a
      | _, _ => none)
  | k + 1, h, t, e, nodes, sibs => do
    match ← levelStep A nodes sibs with
    | none => pure none
    | some (ps, rest) => fold A k (h + 1) t (by omega) ps rest

/-- The root a pruned opening of a tree of depth `depth` claims, from the opened leaves with
their positions and the supplied siblings, with every parent a call of `hash`. -/
def prunedRoot (hash : D → D → m D) (depth : ℕ) (leaves : List (ℕ × D)) (sibs : List D) :
    m (Option D) :=
  fold (NodeAlgebra.ofHash hash) depth 0 depth (Nat.zero_add depth) leaves sibs

/-! ## The walk in `Id` -/

section RunId

variable (A : NodeAlgebra Id D T) {h : ℕ}

/-- Prepend a parent to the node list of a level's result. -/
abbrev consNode {U : Type} (i : ℕ) (p : U) (r : Option (List (ℕ × U) × List D)) :
    Option (List (ℕ × U) × List D) :=
  r.map fun x ↦ ((i, p) :: x.1, x.2)

theorem run_levelStep_nil (sibs : List D) :
    Id.run (levelStep A (h := h) [] sibs) = some ([], sibs) := rfl

theorem run_levelStep_pair (i j : ℕ) (a b : T h) (rest : List (ℕ × T h)) (sibs : List D)
    (hp : i % 2 = 0 ∧ j = i + 1) :
    Id.run (levelStep A ((i, a) :: (j, b) :: rest) sibs) =
      consNode (i / 2) (Id.run (A.both a b)) (Id.run (levelStep A rest sibs)) := by
  simp only [levelStep, hp]
  rfl

theorem run_levelStep_unpaired (i j : ℕ) (a b : T h) (rest : List (ℕ × T h)) (s : D)
    (sibs : List D) (hp : ¬(i % 2 = 0 ∧ j = i + 1)) :
    Id.run (levelStep A ((i, a) :: (j, b) :: rest) (s :: sibs)) =
      consNode (i / 2) (Id.run (withSupplied A i a s))
        (Id.run (levelStep A ((j, b) :: rest) sibs)) := by
  simp only [levelStep, hp, ↓reduceIte]
  rfl

theorem run_levelStep_unpaired_nil (i j : ℕ) (a b : T h) (rest : List (ℕ × T h))
    (hp : ¬(i % 2 = 0 ∧ j = i + 1)) :
    Id.run (levelStep A ((i, a) :: (j, b) :: rest) []) = none := by
  simp only [levelStep, hp, ↓reduceIte]
  rfl

theorem run_levelStep_single (i : ℕ) (a : T h) (s : D) (sibs : List D) :
    Id.run (levelStep A [(i, a)] (s :: sibs)) =
      some ([(i / 2, Id.run (withSupplied A i a s))], sibs) := rfl

theorem run_levelStep_single_nil (i : ℕ) (a : T h) :
    Id.run (levelStep A [(i, a)] []) = none := rfl

theorem run_fold_zero (h : ℕ) (nodes : List (ℕ × T h)) (sibs : List D) :
    Id.run (fold A 0 h (h + 0) rfl nodes sibs) =
      match nodes, sibs with
      | (_, a) :: _, [] => some a
      | _, _ => none := rfl

theorem run_fold_succ (k h t : ℕ) (e : h + (k + 1) = t) (nodes : List (ℕ × T h))
    (sibs : List D) :
    Id.run (fold A (k + 1) h t e nodes sibs) =
      match Id.run (levelStep A nodes sibs) with
      | none => none
      | some (ps, rest) => Id.run (fold A k (h + 1) t (by omega) ps rest) := by
  simp only [fold, Id.run_bind]
  split <;> rfl

end RunId

/-! ## The reading as a VCVio batch opening -/

/-- The selector of a subtree that holds no opened leaf. -/
def unselected : (s : Skeleton) → LeafData Bool s
  | .leaf => .leaf false
  | .internal l r => .internal (unselected l) (unselected r)

theorem anySelected_unselected : ∀ s : Skeleton, (unselected s).anySelected = false
  | .leaf => rfl
  | .internal l r => by
    simp only [unselected, LeafData.anySelected, anySelected_unselected l,
      anySelected_unselected r, Bool.or_self]

/-- The (empty) values of a subtree that holds no opened leaf. -/
def unselectedValues : (s : Skeleton) → SelectedValues D (unselected s)
  | .leaf => PUnit.unit
  | .internal l r => (unselectedValues l, unselectedValues r)

/-- The node algebra of batch openings: a node at height `h` is a batch opening of the perfect
subtree of height `h` below it, and a supplied sibling is the root of a subtree with no opened
leaf. -/
def openingAlgebra : NodeAlgebra Id D fun h ↦ BatchOpening D (Skeleton.perfect h) where
  both a b :=
    ⟨.internal a.selector b.selector, (a.values, b.values), .internalBoth a.proof b.proof⟩
  withRight a s :=
    ⟨.internal a.selector (unselected _), (a.values, unselectedValues _),
      .pruneRight (anySelected_unselected _) s a.proof⟩
  withLeft s b :=
    ⟨.internal (unselected _) b.selector, (unselectedValues _, b.values),
      .pruneLeft (anySelected_unselected _) s b.proof⟩

/-- An opened leaf as the batch opening of a one-leaf tree. -/
def leafOpening (v : D) : BatchOpening D (Skeleton.perfect 0) := ⟨.leaf true, v, .leaf⟩

/-- A pruned opening of the leaves at `positions` of a tree of depth `depth`, read as VCVio's
batch opening: `none` unless the positions strictly increase, lie in the tree and match the
leaves one for one, and the siblings fill the pruned frontier exactly. -/
def toBatchOpening (depth : ℕ) (positions : List ℕ) (leaves sibs : List D) :
    Option (BatchOpening D (Skeleton.perfect depth)) :=
  if positions.Pairwise (· < ·) ∧ (∀ p ∈ positions, p < 2 ^ depth) ∧
      positions.length = leaves.length then
    Id.run (fold openingAlgebra depth 0 depth (Nat.zero_add depth)
      (positions.zip (leaves.map leafOpening)) sibs)
  else none

/-- VCVio's putative root of a batch opening under a node hash. -/
abbrev putativeRoot (hash : D → D → D) {s : Skeleton} (o : BatchOpening D s) : D :=
  getPutativeBatchRootWithHash hash o.values o.proof

section Reading

variable (hash : D → D → D)

/-- A node of the opening walk read as a node of the hash walk. -/
private abbrev rootNode {h : ℕ} (x : ℕ × BatchOpening D (Skeleton.perfect h)) : ℕ × D :=
  (x.1, putativeRoot hash x.2)

private theorem putativeRoot_withSupplied {h : ℕ} (i : ℕ)
    (a : BatchOpening D (Skeleton.perfect h)) (s : D) :
    putativeRoot hash (Id.run (withSupplied openingAlgebra i a s)) =
      Id.run (withSupplied (NodeAlgebra.ofHash (m := Id) hash) (h := h) i
        (putativeRoot hash a) s) := by
  unfold withSupplied
  split <;> rfl

private theorem levelStep_putativeRoot {h : ℕ} :
    ∀ (nodes : List (ℕ × BatchOpening D (Skeleton.perfect h))) (sibs : List D),
      Id.run (levelStep (NodeAlgebra.ofHash (m := Id) hash) (h := h)
          (nodes.map (rootNode hash)) sibs) =
        (Id.run (levelStep openingAlgebra nodes sibs)).map
          fun r ↦ (r.1.map (rootNode hash), r.2)
  | [], _ => rfl
  | (i, a) :: (j, b) :: rest, sibs => by
    rw [List.map_cons, List.map_cons]
    by_cases hp : i % 2 = 0 ∧ j = i + 1
    · rw [run_levelStep_pair _ _ _ _ _ _ _ hp, run_levelStep_pair _ _ _ _ _ _ _ hp,
        levelStep_putativeRoot rest sibs]
      cases Id.run (levelStep openingAlgebra rest sibs) <;> rfl
    · cases sibs with
      | nil =>
        rw [run_levelStep_unpaired_nil _ _ _ _ _ _ hp, run_levelStep_unpaired_nil _ _ _ _ _ _ hp]
        rfl
      | cons s sibs =>
        have ih := levelStep_putativeRoot ((j, b) :: rest) sibs
        rw [List.map_cons] at ih
        rw [run_levelStep_unpaired _ _ _ _ _ _ _ _ hp, run_levelStep_unpaired _ _ _ _ _ _ _ _ hp,
          ih, ← putativeRoot_withSupplied]
        cases Id.run (levelStep openingAlgebra ((j, b) :: rest) sibs) <;> rfl
  | [(i, a)], sibs => by
    cases sibs with
    | nil => rfl
    | cons s sibs =>
      rw [List.map_cons, List.map_nil, run_levelStep_single, run_levelStep_single,
        ← putativeRoot_withSupplied]
      rfl

private theorem fold_putativeRoot :
    ∀ (k h t : ℕ) (e : h + k = t) (nodes : List (ℕ × BatchOpening D (Skeleton.perfect h)))
      (sibs : List D),
      Id.run (fold (NodeAlgebra.ofHash (m := Id) hash) k h t e
          (nodes.map (rootNode hash)) sibs) =
        (Id.run (fold openingAlgebra k h t e nodes sibs)).map (putativeRoot hash)
  | 0, h, t, e, nodes, sibs => by
    subst e
    rw [run_fold_zero, run_fold_zero]
    rcases nodes with _ | ⟨⟨_, a⟩, _⟩ <;> rcases sibs with _ | _ <;> rfl
  | k + 1, h, t, e, nodes, sibs => by
    rw [run_fold_succ, run_fold_succ, levelStep_putativeRoot]
    rcases Id.run (levelStep openingAlgebra nodes sibs) with _ | ⟨ps, rest⟩
    · rfl
    · exact fold_putativeRoot k (h + 1) t _ ps rest

/-- The reading: for every node hash, `toBatchOpening` reads a pruned opening as a VCVio batch
opening whose putative root is `r` exactly when the positions strictly increase, lie in the tree
and match the leaves one for one, and the walk reaches `r`. -/
theorem prunedRoot_eq_some_iff (depth : ℕ) (positions : List ℕ) (leaves sibs : List D) (r : D) :
    (∃ o, toBatchOpening depth positions leaves sibs = some o ∧ putativeRoot hash o = r) ↔
      (positions.Pairwise (· < ·) ∧ (∀ p ∈ positions, p < 2 ^ depth) ∧
        positions.length = leaves.length) ∧
      Id.run (prunedRoot (m := Id) hash depth (positions.zip leaves) sibs) = some r := by
  have hmap : positions.zip leaves =
      (positions.zip (leaves.map leafOpening)).map (rootNode hash) := by
    rw [List.zip_map_right, List.map_map]
    exact (List.map_id'' (fun _ ↦ rfl) _).symm
  unfold toBatchOpening prunedRoot
  rw [hmap, fold_putativeRoot, Option.map_eq_some_iff]
  split
  · next hv => exact ⟨fun h ↦ ⟨hv, h⟩, fun h ↦ h.2⟩
  · next hv =>
    constructor
    · rintro ⟨o, ho, _⟩
      cases ho
    · rintro ⟨h, _⟩
      exact absurd h hv

end Reading

/-! ## The honest prover -/

section Prover

variable (hashPair : D → D → D)

/-- The index of the node sharing a parent with node `i`: `i + 1` at an even index, `i - 1` at
an odd one (`i ^^^ 1`). -/
def sibling (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

/-- The parent indices of a level's opened nodes, sorted by index, as `levelStep` forms them. -/
def parentPositions : List ℕ → List ℕ
  | [] => []
  | i :: tl =>
    match tl with
    | j :: rest =>
      if i % 2 = 0 ∧ j = i + 1 then i / 2 :: parentPositions rest
      else i / 2 :: parentPositions (j :: rest)
    | [] => [i / 2]
termination_by structural ps => ps

/-- The siblings a level of an opening supplies, left to right: the sibling of every opened
node that is not paired with the next. -/
def levelSiblings {n : ℕ} (level : Vector D n) : List ℕ → List D
  | [] => []
  | i :: tl =>
    match tl with
    | j :: rest =>
      if i % 2 = 0 ∧ j = i + 1 then levelSiblings level rest
      else level[sibling i]?.toList ++ levelSiblings level (j :: rest)
    | [] => level[sibling i]?.toList
termination_by structural ps => ps

/-- The siblings of the pruned opening at `positions` of the tree over a level of `2^k` nodes,
bottom-up and left to right. -/
def openSiblings : (k : ℕ) → Vector D (2 ^ k) → List ℕ → List D
  | 0, _, _ => []
  | k + 1, level, positions =>
    levelSiblings level positions ++
      openSiblings k (parents hashPair level) (parentPositions positions)

/-- The opened nodes of a level at `positions`, with their values. -/
def nodesAt {n : ℕ} (level : Vector D n) (positions : List ℕ) : List (ℕ × D) :=
  positions.filterMap fun p ↦ level[p]?.map (p, ·)

/-- The opened nodes at a position in the level and further positions. -/
theorem nodesAt_cons {n : ℕ} (level : Vector D n) {p : ℕ} (hp : p < n)
    (ps : List ℕ) : nodesAt level (p :: ps) = (p, level[p]) :: nodesAt level ps := by
  simp [nodesAt, hp]

private theorem sibling_lt {k i : ℕ} (hi : i < 2 ^ (k + 1)) : sibling i < 2 ^ (k + 1) := by
  unfold sibling; rw [Nat.pow_succ] at *; split <;> omega

private theorem parents_getElem_even {k : ℕ} (level : Vector D (2 ^ (k + 1))) {i : ℕ}
    (he : i % 2 = 0) (hlt : i + 1 < 2 ^ (k + 1)) :
    (parents hashPair level)[i / 2]'(by rw [Nat.pow_succ] at hlt; omega) =
      hashPair (level[i]'(by omega)) level[i + 1] := by
  simp only [parents, Vector.getElem_ofFn, show 2 * (i / 2) = i by omega]

private theorem parents_getElem_odd {k : ℕ} (level : Vector D (2 ^ (k + 1))) {i : ℕ}
    (ho : i % 2 = 1) (hlt : i < 2 ^ (k + 1)) :
    (parents hashPair level)[i / 2]'(by rw [Nat.pow_succ] at hlt; omega) =
      hashPair (level[i - 1]'(by omega)) level[i] := by
  simp only [parents, Vector.getElem_ofFn, show 2 * (i / 2) = i - 1 by omega,
    show i - 1 + 1 = i by omega]

/-- The parent of node `i` is the hash of `i` and its sibling, in index order. -/
private theorem parents_getElem {k : ℕ} (level : Vector D (2 ^ (k + 1))) {i : ℕ}
    (hi : i < 2 ^ (k + 1)) :
    (parents hashPair level)[i / 2]'(by rw [Nat.pow_succ] at hi; omega) =
      Id.run (withSupplied (NodeAlgebra.ofHash (m := Id) hashPair) (h := 0) i level[i]
        (level[sibling i]'(sibling_lt hi))) := by
  by_cases he : i % 2 = 0
  · have hlt : i + 1 < 2 ^ (k + 1) := by
      have := sibling_lt hi; simp only [sibling, he, ↓reduceIte] at this; exact this
    simp only [withSupplied, sibling, he, ↓reduceIte]
    exact parents_getElem_even hashPair level he hlt
  · simp only [withSupplied, sibling, he, ↓reduceIte]
    exact parents_getElem_odd hashPair level (by omega) hi

/-- One level of the honest opening: the walk pairs the opened nodes as the prover did, uses up
exactly the prover's siblings of the level, and reaches the opened nodes of the parent level. -/
private theorem levelStep_nodesAt {k h : ℕ} (level : Vector D (2 ^ (k + 1))) :
    ∀ (positions : List ℕ) (rest : List D), (∀ p ∈ positions, p < 2 ^ (k + 1)) →
      Id.run (levelStep (NodeAlgebra.ofHash (m := Id) hashPair) (h := h)
          (nodesAt level positions) (levelSiblings level positions ++ rest)) =
        some (nodesAt (parents hashPair level) (parentPositions positions), rest)
  | [], _, _ => rfl
  | i :: j :: ps, rest, hlt => by
    have hi := hlt i (by simp)
    have hj := hlt j (by simp)
    have hpar : i / 2 < 2 ^ k := by rw [Nat.pow_succ] at hi; omega
    rw [nodesAt_cons level hi, nodesAt_cons level hj]
    by_cases hp : i % 2 = 0 ∧ j = i + 1
    · have hps : ∀ p ∈ ps, p < 2 ^ (k + 1) := fun p hp ↦ hlt p (by simp [hp])
      rw [run_levelStep_pair _ _ _ _ _ _ _ hp]
      obtain ⟨he, rfl⟩ := hp
      simp only [levelSiblings, parentPositions, he, and_self, ↓reduceIte]
      rw [levelStep_nodesAt level ps rest hps, nodesAt_cons _ hpar,
        parents_getElem_even hashPair level he hj]
      rfl
    · have hs := sibling_lt (k := k) hi
      simp only [levelSiblings, parentPositions, hp, ↓reduceIte]
      rw [show level[sibling i]? = some level[sibling i] by simp [hs], Option.toList_some,
        List.singleton_append, List.cons_append, run_levelStep_unpaired _ _ _ _ _ _ _ _ hp,
        ← nodesAt_cons level hj,
        levelStep_nodesAt level (j :: ps) rest (fun p hp ↦ hlt p (List.mem_cons_of_mem _ hp)),
        nodesAt_cons _ hpar, parents_getElem hashPair level hi]
      rfl
  | [i], rest, hlt => by
    have hi := hlt i (by simp)
    have hs := sibling_lt (k := k) hi
    have hpar : i / 2 < 2 ^ k := by rw [Nat.pow_succ] at hi; omega
    simp only [levelSiblings, parentPositions]
    rw [nodesAt_cons level hi, show level[sibling i]? = some level[sibling i] by simp [hs],
      Option.toList_some, List.singleton_append, show nodesAt level [] = [] from rfl,
      run_levelStep_single, nodesAt_cons _ hpar, parents_getElem hashPair level hi]
    rfl

private theorem parentPositions_ne_nil : ∀ {ps : List ℕ}, ps ≠ [] → parentPositions ps ≠ []
  | [], h => absurd rfl h
  | _ :: _ :: _, _ => by simp only [parentPositions]; split <;> simp
  | [_], _ => by simp [parentPositions]

private theorem parentPositions_lt {k : ℕ} :
    ∀ (ps : List ℕ), (∀ p ∈ ps, p < 2 ^ (k + 1)) → ∀ q ∈ parentPositions ps, q < 2 ^ k
  | [], _ => by simp [parentPositions]
  | i :: j :: ps, h => by
    have hi := h i (by simp)
    have hi' : i / 2 < 2 ^ k := by rw [Nat.pow_succ] at hi; omega
    simp only [parentPositions]
    split
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hi'
      · exact parentPositions_lt ps (fun p hp ↦ h p (by simp [hp])) q hq
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hi'
      · exact parentPositions_lt (j :: ps) (fun p hp ↦ h p (List.mem_cons_of_mem _ hp)) q hq
  | [i], h => by
    have hi := h i (by simp)
    simp only [parentPositions, List.mem_singleton]
    rintro q rfl
    rw [Nat.pow_succ] at hi; omega

/-- Completeness: the honest opening of a tree at nonempty positions in the tree reaches the
tree's root, with every sibling used. -/
theorem prunedRoot_openSiblings {k : ℕ} (level : Vector D (2 ^ k)) (positions : List ℕ)
    (hne : positions ≠ []) (hlt : ∀ p ∈ positions, p < 2 ^ k) :
    Id.run (prunedRoot (m := Id) hashPair k (nodesAt level positions)
        (openSiblings hashPair k level positions)) =
      some (rootOfLevel hashPair k level) := by
  unfold prunedRoot
  suffices ∀ (k h t : ℕ) (e : h + k = t) (level : Vector D (2 ^ k)) (positions : List ℕ),
      positions ≠ [] → (∀ p ∈ positions, p < 2 ^ k) →
      Id.run (fold (NodeAlgebra.ofHash (m := Id) hashPair) k h t e (nodesAt level positions)
          (openSiblings hashPair k level positions)) =
        some (rootOfLevel hashPair k level) from this k 0 k _ level positions hne hlt
  intro k
  induction k with
  | zero =>
    intro h t e level positions hne hlt
    subst e
    obtain ⟨p, ps, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hp : p = 0 := by have := hlt p (by simp); simpa using this
    subst hp
    rw [nodesAt_cons level (by simp), run_fold_zero]
    rfl
  | succ k ih =>
    intro h t e level positions hne hlt
    rw [run_fold_succ, openSiblings, levelStep_nodesAt hashPair level positions _ hlt]
    exact ih (h + 1) t _ _ _ (parentPositions_ne_nil hne) (parentPositions_lt positions hlt)

end Prover

/-! ## The tree built once -/

section Levels

variable (hashPair : D → D → D)

/-- The levels of a tree, bottom-up: a level of `2^(k+1)` nodes above which stand the levels of
its parents, up to the root. -/
inductive Levels (D : Type) : ℕ → Type
  | top (root : D) : Levels D 0
  | cons {k : ℕ} (level : Vector D (2 ^ (k + 1))) (above : Levels D k) : Levels D (k + 1)

/-- The levels of the tree over a level of `2^k` nodes, each level's parents hashed once. -/
def buildLevels : (k : ℕ) → Vector D (2 ^ k) → Levels D k
  | 0, level => .top level[0]
  | k + 1, level => .cons level (buildLevels k (parents hashPair level))

/-- The root of a tree's levels. -/
def Levels.root : {k : ℕ} → Levels D k → D
  | _, .top r => r
  | _, .cons _ above => above.root

/-- The siblings of the pruned opening at `positions`, read off a tree's levels, bottom-up and
left to right. -/
def Levels.siblings : {k : ℕ} → Levels D k → List ℕ → List D
  | _, .top _, _ => []
  | _, .cons level above, positions =>
    levelSiblings level positions ++ above.siblings (parentPositions positions)

theorem root_buildLevels : ∀ (k : ℕ) (level : Vector D (2 ^ k)),
    (buildLevels hashPair k level).root = rootOfLevel hashPair k level
  | 0, _ => rfl
  | k + 1, level => root_buildLevels k (parents hashPair level)

theorem siblings_buildLevels : ∀ (k : ℕ) (level : Vector D (2 ^ k)) (positions : List ℕ),
    (buildLevels hashPair k level).siblings positions = openSiblings hashPair k level positions
  | 0, _, _ => rfl
  | k + 1, level, positions => by
    simp only [buildLevels, Levels.siblings, openSiblings,
      siblings_buildLevels k (parents hashPair level)]

end Levels

/-! ## The query model of an untagged node hash -/

/-- The VCVio query model of a node hash that queries the encodings of its two children, left
first, with no address: a query is decoded by splitting it at the encoding's length. -/
def nodeQueryModelOfEncoding {B : Type} (encode : D → List B) (decode : List B → D) (n : ℕ)
    (length_encode : ∀ d, (encode d).length = n) (decode_encode : ∀ d, decode (encode d) = d) :
    MerkleTreeExtractability.NodeQueryModel (List B) Unit D where
  view := { address := fun _ ↦ (), input := fun q ↦ (decode (q.take n), decode (q.drop n)) }
  mkQuery _ lr := encode lr.1 ++ encode lr.2
  address_mkQuery _ _ := rfl
  input_mkQuery _ lr := by
    obtain ⟨l, r⟩ := lr
    have h1 : (encode l ++ encode r).take n = encode l := by
      rw [← length_encode l, List.take_left]
    have h2 : (encode l ++ encode r).drop n = encode r := by
      rw [← length_encode l, List.drop_left]
    simp only [h1, h2, decode_encode]

end
end LeanerVM.Protocol.MerkleTree
