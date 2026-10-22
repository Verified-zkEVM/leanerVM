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
`fold_map` carries the walk along a map of node algebras, of which the reading is an instance.
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
  Vector.ofFn fun j ↦ hashPair (level[2 * j.val]'(by omega)) (level[2 * j.val + 1]'(by omega))

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
      consNode (i / 2) (Id.run (A.both a b)) (Id.run (levelStep A rest sibs)) :=
  congrArg Id.run (ite_eq_left hp)

theorem run_levelStep_unpaired (i j : ℕ) (a b : T h) (rest : List (ℕ × T h)) (s : D)
    (sibs : List D) (hp : ¬(i % 2 = 0 ∧ j = i + 1)) :
    Id.run (levelStep A ((i, a) :: (j, b) :: rest) (s :: sibs)) =
      consNode (i / 2) (Id.run (withSupplied A i a s))
        (Id.run (levelStep A ((j, b) :: rest) sibs)) :=
  congrArg Id.run (ite_eq_right hp)

theorem run_levelStep_unpaired_nil (i j : ℕ) (a b : T h) (rest : List (ℕ × T h))
    (hp : ¬(i % 2 = 0 ∧ j = i + 1)) :
    Id.run (levelStep A ((i, a) :: (j, b) :: rest) []) = none :=
  congrArg Id.run (ite_eq_right hp)

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
      | some (ps, rest) => Id.run (fold A k (h + 1) t (by omega) ps rest) := rfl

end RunId

/-! ## Maps of node algebras -/

section Map

variable [LawfulMonad m] {T' : ℕ → Type}

/-- A level's result with every node carried along `f`. -/
abbrev mapLevel {U U' : Type} (f : U → U') :
    Option (List (ℕ × U) × List D) → Option (List (ℕ × U') × List D) :=
  Option.map fun r ↦ (r.1.map fun x ↦ (x.1, f x.2), r.2)

private theorem consParent_map {U U' : Type} (f : U → U') (i : ℕ) (p : m U)
    (r : m (Option (List (ℕ × U) × List D))) :
    consParent i (f <$> p) (mapLevel f <$> r) = mapLevel f <$> consParent i p r := by
  simp only [consParent, map_eq_pure_bind, bind_assoc, pure_bind, mapLevel, Option.map_map]
  rfl

/-- One level of the walk commutes with a map `φ` of node algebras: a map that carries each
operation of `A` to that of `B`. -/
theorem levelStep_map (A : NodeAlgebra m D T) (B : NodeAlgebra m D T')
    (φ : ∀ {h : ℕ}, T h → T' h)
    (hboth : ∀ {h : ℕ} (a b : T h), B.both (φ a) (φ b) = φ <$> A.both a b)
    (hright : ∀ {h : ℕ} (a : T h) (s : D), B.withRight (φ a) s = φ <$> A.withRight a s)
    (hleft : ∀ {h : ℕ} (s : D) (b : T h), B.withLeft s (φ b) = φ <$> A.withLeft s b) {h : ℕ} :
    ∀ (nodes : List (ℕ × T h)) (sibs : List D),
      levelStep B (nodes.map fun x ↦ (x.1, φ x.2)) sibs = mapLevel φ <$> levelStep A nodes sibs
  | [], sibs => by simp [levelStep, mapLevel]
  | (i, a) :: (j, b) :: rest, sibs => by
    have hsup : ∀ s, withSupplied B i (φ a) s = φ <$> withSupplied A i a s := fun s ↦ by
      unfold withSupplied; split
      · exact hright a s
      · exact hleft s a
    simp only [List.map_cons]
    by_cases hp : i % 2 = 0 ∧ j = i + 1
    · simp only [levelStep, hp, and_self, ↓reduceIte]
      rw [hboth, levelStep_map A B φ hboth hright hleft rest sibs, consParent_map]
    · simp only [levelStep, hp, ↓reduceIte]
      cases sibs with
      | nil => simp [withNext, mapLevel]
      | cons s sibs =>
        have ih := levelStep_map A B φ hboth hright hleft ((j, b) :: rest) sibs
        simp only [List.map_cons] at ih
        simp only [withNext]
        rw [hsup, ih, consParent_map]
  | [(i, a)], sibs => by
    cases sibs with
    | nil => simp [levelStep, withNext, mapLevel]
    | cons s sibs =>
      have hsup : withSupplied B i (φ a) s = φ <$> withSupplied A i a s := by
        unfold withSupplied; split
        · exact hright a s
        · exact hleft s a
      simp only [List.map_cons, List.map_nil, levelStep, withNext]
      rw [hsup]
      simpa [mapLevel] using
        consParent_map (D := D) φ (i / 2) (withSupplied A i a s) (pure (some ([], sibs)))

/-- The walk commutes with a map `φ` of node algebras: walking the images of the opened nodes
under `B` gives the image of `A`'s walk. -/
theorem fold_map (A : NodeAlgebra m D T) (B : NodeAlgebra m D T')
    (φ : ∀ {h : ℕ}, T h → T' h)
    (hboth : ∀ {h : ℕ} (a b : T h), B.both (φ a) (φ b) = φ <$> A.both a b)
    (hright : ∀ {h : ℕ} (a : T h) (s : D), B.withRight (φ a) s = φ <$> A.withRight a s)
    (hleft : ∀ {h : ℕ} (s : D) (b : T h), B.withLeft s (φ b) = φ <$> A.withLeft s b) :
    ∀ (k h t : ℕ) (e : h + k = t) (nodes : List (ℕ × T h)) (sibs : List D),
      fold B k h t e (nodes.map fun x ↦ (x.1, φ x.2)) sibs =
        Option.map φ <$> fold A k h t e nodes sibs
  | 0, h, t, e, nodes, sibs => by
    subst e
    simp only [fold, map_pure]
    rcases nodes with _ | ⟨⟨_, a⟩, _⟩ <;> rcases sibs with _ | _ <;> rfl
  | k + 1, h, t, e, nodes, sibs => by
    simp only [fold]
    rw [levelStep_map A B φ hboth hright hleft, bind_map_left, map_bind]
    congr 1; funext r
    rcases r with _ | ⟨ps, rest⟩
    · simp
    · exact fold_map A B φ hboth hright hleft k (h + 1) t _ ps rest

end Map

/-! ## The reading as a VCVio batch opening -/

/-- The selector of a subtree that holds no opened leaf. -/
def unselected : (s : Skeleton) → LeafData Bool s
  | .leaf => .leaf false
  | .internal l r => .internal (unselected l) (unselected r)

theorem anySelected_unselected : ∀ s : Skeleton, (unselected s).anySelected = false
  | .leaf => rfl
  | .internal l r => by
    simp only [unselected, LeafData.anySelected, anySelected_unselected, Bool.or_self]

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

/-- The putative root is a map of node algebras from the batch openings to the node hash. -/
private theorem fold_putativeRoot (k h t : ℕ) (e : h + k = t)
    (nodes : List (ℕ × BatchOpening D (Skeleton.perfect h))) (sibs : List D) :
    Id.run (fold (NodeAlgebra.ofHash (m := Id) hash) k h t e
        (nodes.map (rootNode hash)) sibs) =
      (Id.run (fold openingAlgebra k h t e nodes sibs)).map (putativeRoot hash) :=
  fold_map openingAlgebra (NodeAlgebra.ofHash hash) (putativeRoot hash) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) k h t e nodes sibs

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
  · next hv => exact ⟨fun ⟨_, ho, _⟩ ↦ (nomatch ho), fun h ↦ absurd h.1 hv⟩

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

private theorem half_lt {k i : ℕ} (hi : i < 2 ^ (k + 1)) : i / 2 < 2 ^ k := by omega

private theorem sibling_lt {k i : ℕ} (hi : i < 2 ^ (k + 1)) : sibling i < 2 ^ (k + 1) := by
  unfold sibling
  split <;> omega

/-- The parent of node `i` is the hash of `i` and its sibling, in index order. -/
private theorem parents_getElem {k : ℕ} (level : Vector D (2 ^ (k + 1))) {i : ℕ}
    (hi : i < 2 ^ (k + 1)) :
    (parents hashPair level)[i / 2]'(half_lt hi) =
      Id.run (withSupplied (NodeAlgebra.ofHash (m := Id) hashPair) (h := 0) i level[i]
        (level[sibling i]'(sibling_lt hi))) := by
  have hm := Nat.div_add_mod i 2
  simp only [parents, Vector.getElem_ofFn]
  unfold withSupplied sibling
  split_ifs with he
  · rw [he] at hm
    exact congrArg₂ hashPair (getElem_congr_idx hm) (getElem_congr_idx (congrArg (· + 1) hm))
  · rw [Nat.mod_two_ne_zero.mp he] at hm
    exact congrArg₂ hashPair (getElem_congr_idx (Nat.eq_sub_of_add_eq hm)) (getElem_congr_idx hm)

/-- One level of the honest opening: the walk pairs the opened nodes as the prover did, uses up
exactly the prover's siblings of the level, and reaches the opened nodes of the parent level. -/
private theorem levelStep_nodesAt {k h : ℕ} (level : Vector D (2 ^ (k + 1))) :
    ∀ (positions : List ℕ) (rest : List D), (∀ p ∈ positions, p < 2 ^ (k + 1)) →
      Id.run (levelStep (NodeAlgebra.ofHash (m := Id) hashPair) (h := h)
          (nodesAt level positions) (levelSiblings level positions ++ rest)) =
        some (nodesAt (parents hashPair level) (parentPositions positions), rest)
  | [], _, _ => rfl
  | i :: j :: ps, rest, hlt => by
    obtain ⟨hi, hjps⟩ := List.forall_mem_cons.mp hlt
    obtain ⟨hj, hps⟩ := List.forall_mem_cons.mp hjps
    rw [nodesAt_cons level hi, nodesAt_cons level hj]
    by_cases hp : i % 2 = 0 ∧ j = i + 1
    · rw [run_levelStep_pair _ _ _ _ _ _ _ hp]
      obtain ⟨he, rfl⟩ := hp
      simp only [levelSiblings, parentPositions, he, and_self, ↓reduceIte]
      rw [levelStep_nodesAt level ps rest hps, nodesAt_cons _ (half_lt hi),
        parents_getElem hashPair level hi]
      simp only [withSupplied, sibling, he, ↓reduceIte]
      rfl
    · simp only [levelSiblings, parentPositions, hp, ↓reduceIte]
      rw [Vector.getElem?_eq_getElem (sibling_lt hi), Option.toList_some, List.singleton_append,
        List.cons_append, run_levelStep_unpaired _ _ _ _ _ _ _ _ hp, ← nodesAt_cons level hj,
        levelStep_nodesAt level (j :: ps) rest hjps, nodesAt_cons _ (half_lt hi),
        parents_getElem hashPair level hi]
      rfl
  | [i], rest, hlt => by
    have hi := hlt i List.mem_cons_self
    simp only [levelSiblings, parentPositions]
    rw [nodesAt_cons level hi, Vector.getElem?_eq_getElem (sibling_lt hi), Option.toList_some,
      List.singleton_append, show nodesAt level [] = [] from rfl, run_levelStep_single,
      nodesAt_cons _ (half_lt hi), parents_getElem hashPair level hi]
    rfl

private theorem parentPositions_ne_nil : ∀ {ps : List ℕ}, ps ≠ [] → parentPositions ps ≠ []
  | [], h => h
  | _ :: _ :: _, _ => by
    simp only [parentPositions]
    split <;> exact List.cons_ne_nil _ _
  | [_], _ => List.cons_ne_nil _ _

/-- The parent positions are the positions halved, some dropped. -/
private theorem parentPositions_sublist :
    ∀ ps : List ℕ, (parentPositions ps).Sublist (ps.map (· / 2))
  | [] => .slnil
  | [_] => .refl _
  | i :: j :: ps => by
    simp only [parentPositions]
    split
    · exact ((parentPositions_sublist ps).cons _).cons_cons _
    · exact (parentPositions_sublist (j :: ps)).cons_cons _

private theorem parentPositions_lt {k : ℕ} {ps : List ℕ} (h : ∀ p ∈ ps, p < 2 ^ (k + 1))
    {q : ℕ} (hq : q ∈ parentPositions ps) : q < 2 ^ k := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((parentPositions_sublist ps).subset hq)
  have := h p hp
  omega

private theorem fold_openSiblings :
    ∀ (k h t : ℕ) (e : h + k = t) (level : Vector D (2 ^ k)) (positions : List ℕ),
      positions ≠ [] → (∀ p ∈ positions, p < 2 ^ k) →
      Id.run (fold (NodeAlgebra.ofHash (m := Id) hashPair) k h t e (nodesAt level positions)
          (openSiblings hashPair k level positions)) =
        some (rootOfLevel hashPair k level)
  | 0, _, _, rfl, _, [], hne, _ => absurd rfl hne
  | 0, _, _, rfl, level, p :: _, _, hlt => by
    obtain rfl := Nat.lt_one_iff.mp (hlt p List.mem_cons_self)
    rw [nodesAt_cons level Nat.zero_lt_one]
    rfl
  | k + 1, h, t, e, level, positions, hne, hlt => by
    rw [run_fold_succ, openSiblings, levelStep_nodesAt hashPair level positions _ hlt]
    exact fold_openSiblings k (h + 1) t _ _ _ (parentPositions_ne_nil hne)
      fun _ ↦ parentPositions_lt hlt

/-- Completeness: the honest opening of a tree at nonempty positions in the tree reaches the
tree's root, with every sibling used. -/
theorem prunedRoot_openSiblings {k : ℕ} (level : Vector D (2 ^ k)) (positions : List ℕ)
    (hne : positions ≠ []) (hlt : ∀ p ∈ positions, p < 2 ^ k) :
    Id.run (prunedRoot (m := Id) hashPair k (nodesAt level positions)
        (openSiblings hashPair k level positions)) =
      some (rootOfLevel hashPair k level) :=
  fold_openSiblings hashPair k 0 k _ level positions hne hlt

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
  | k + 1, level, positions =>
    congrArg (levelSiblings level positions ++ ·) (siblings_buildLevels k _ _)

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
    simp only [List.take_left' (length_encode _), List.drop_left' (length_encode _),
      decode_encode]

end
end LeanerVM.Protocol.MerkleTree
