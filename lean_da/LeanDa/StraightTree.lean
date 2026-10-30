import LeanDa.RpmWagner
import LeanDa.MerkleM

/-!
# The commitment's tree, read off the hash calls

For the straight-line proof of code binding (`LeanDa.Straight`): the hash inputs of a commitment
(`commitIn`, the cells' bytes, the rows' leaves, the two trees' nodes and the root's
`rowRoot ‖ colRoot`) and of an opening's check (`verifyIn`), for a hash function `f`, and what
they give when `f` is injective on a set holding them.

* **Every input but the root's hashes to a digest the commitment's inputs carry**
  (`commitIn_parent`): a node's digest is a 32-byte block (`chunks`) of its parent's input.
* **The commitment depends on `f` only on its inputs** (`commitIn_congr`).
* **One root, one matrix** (`commit_unique`), and **an opening that verifies against a root opens
  the matrix's cell** (`verifyCell_agree`), when `f` is injective on a set holding the inputs.
* **Over a partial hash** (`Option`, a cache's lookups), a commitment or a check that returns
  has its inputs in the hash's domain and its pure value (`commitCellsM_some`,
  `verifyCellM_some`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA; the
straight-line proof it serves replaces his forking step and keeps his framework and games.
-/

set_option linter.unusedSectionVars false

namespace LeanDa

/-! ## The digests an input carries -/

/-- Block `t` of a string: its bytes `32 t … 32 t + 31`, as a digest. -/
def chunkAt (b : List UInt8) (t : ℕ) : Common.DigestBytes := Vector.ofFn fun i : Fin 32 ↦ b.getD (32 * t + i) 0

/-- **The digests a hash input carries**: its 32-byte blocks, for the inputs of `64` bytes (a
node's two children) and `2048` bytes (a row's leaf, its `64` cell digests). -/
def chunks (b : List UInt8) : Finset Common.DigestBytes :=
  if b.length = 64 ∨ b.length = 2048 then (Finset.range (b.length / 32)).image (chunkAt b) else ∅

theorem card_chunks_le (b : List UInt8) : (chunks b).card ≤ 64 := by
  unfold chunks
  split
  · next h =>
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_range]
    omega
  · simp

theorem chunkAt_append_left (a : Common.DigestBytes) (l : List UInt8) : chunkAt (a.toList ++ l) 0 = a := by
  apply Vector.ext
  intro i hi
  simp only [chunkAt, Vector.getElem_ofFn, Nat.mul_zero, Nat.zero_add]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simpa using hi),
    Vector.getElem_toList]

theorem chunkAt_append_succ (a : Common.DigestBytes) (l : List UInt8) (t : ℕ) :
    chunkAt (a.toList ++ l) (t + 1) = chunkAt l t := by
  apply Vector.ext
  intro i hi
  simp only [chunkAt, Vector.getElem_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp; omega)]
  congr 2
  simp only [Vector.length_toList]
  omega

theorem chunkAt_pairBytes_zero (a b : Common.DigestBytes) : chunkAt (pairBytes a b) 0 = a :=
  chunkAt_append_left a _

theorem chunkAt_pairBytes_one (a b : Common.DigestBytes) : chunkAt (pairBytes a b) 1 = b := by
  rw [pairBytes, chunkAt_append_succ, ← List.append_nil b.toList, chunkAt_append_left]

theorem mem_chunks_pairBytes_left (a b : Common.DigestBytes) : a ∈ chunks (pairBytes a b) := by
  unfold chunks
  rw [ite_eq_left (Or.inl (length_pairBytes a b))]
  exact Finset.mem_image.mpr ⟨0, by simp [length_pairBytes], chunkAt_pairBytes_zero a b⟩

theorem mem_chunks_pairBytes_right (a b : Common.DigestBytes) : b ∈ chunks (pairBytes a b) := by
  unfold chunks
  rw [ite_eq_left (Or.inl (length_pairBytes a b))]
  exact Finset.mem_image.mpr ⟨1, by simp [length_pairBytes], chunkAt_pairBytes_one a b⟩

/-! ## The inputs of a Merkle tree -/

variable (f : List UInt8 → Common.DigestBytes)

/-- **The inputs a Merkle tree of depth `d` over the leaves `L` hashes**, level by level. -/
def merkleIn : ℕ → (ℕ → Common.DigestBytes) → Set (List UInt8)
  | 0, _ => ∅
  | d + 1, L => {a | ∃ i < 2 ^ d, a = pairBytes (L (2 * i)) (L (2 * i + 1))} ∪ merkleIn d (up f L)

theorem merkleIn_succ (d : ℕ) (L : ℕ → Common.DigestBytes) :
    merkleIn f (d + 1) L =
      {a | ∃ i < 2 ^ d, a = pairBytes (L (2 * i)) (L (2 * i + 1))} ∪ merkleIn f d (up f L) := rfl

theorem pair_mem_merkleIn (d : ℕ) (L : ℕ → Common.DigestBytes) (i : ℕ) (hi : i < 2 ^ d) :
    pairBytes (L (2 * i)) (L (2 * i + 1)) ∈ merkleIn f (d + 1) L :=
  Or.inl ⟨i, hi, rfl⟩

/-- **The tree depends on the hash only on its inputs**, and on the leaves only on its own. -/
theorem merkleIn_congr (f' : List UInt8 → Common.DigestBytes) (d : ℕ) :
    ∀ L L' : ℕ → Common.DigestBytes, (∀ i < 2 ^ d, L i = L' i) → (∀ a ∈ merkleIn f d L, f a = f' a) →
      merkleIn f' d L' = merkleIn f d L ∧ merkleRoot f' d L' = merkleRoot f d L := by
  induction d with
  | zero =>
    intro L L' hL _
    exact ⟨rfl, (hL 0 (by norm_num)).symm⟩
  | succ d ih =>
    intro L L' hL hf
    have hL2 : ∀ i < 2 ^ d, L (2 * i) = L' (2 * i) ∧ L (2 * i + 1) = L' (2 * i + 1) :=
      fun i hi ↦ ⟨hL _ (by rw [pow_succ]; omega), hL _ (by rw [pow_succ]; omega)⟩
    have hup : ∀ i < 2 ^ d, up f L i = up f' L' i := fun i hi ↦ by
      simp only [up]
      rw [hf _ (pair_mem_merkleIn f d L i hi), (hL2 i hi).1, (hL2 i hi).2]
    obtain ⟨h1, h2⟩ := ih (up f L) (up f' L') hup fun a ha ↦ hf a (Or.inr ha)
    refine ⟨?_, h2⟩
    rw [merkleIn_succ, merkleIn_succ, h1]
    congr 1
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, by rw [(hL2 i hi).1, (hL2 i hi).2]⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, by rw [(hL2 i hi).1, (hL2 i hi).2]⟩

/-- **A leaf is the root or a digest an input carries.** -/
theorem leaf_mem (d : ℕ) (L : ℕ → Common.DigestBytes) (i : ℕ) (hi : i < 2 ^ d) :
    L i = merkleRoot f d L ∨ ∃ b ∈ merkleIn f d L, L i ∈ chunks b := by
  rcases d with _ | d
  · obtain rfl : i = 0 := by simpa using hi
    exact Or.inl rfl
  · refine Or.inr ⟨_, pair_mem_merkleIn f d L (i / 2) (by rw [pow_succ] at hi; omega), ?_⟩
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [show 2 * (i / 2) = i by omega]; exact mem_chunks_pairBytes_left _ _
    · rw [show 2 * (i / 2) + 1 = i by omega]; exact mem_chunks_pairBytes_right _ _

/-- **An input hashes to the root or to a digest an input carries.** -/
theorem merkleIn_parent (d : ℕ) :
    ∀ (L : ℕ → Common.DigestBytes) (a : List UInt8), a ∈ merkleIn f d L →
      f a = merkleRoot f d L ∨ ∃ b ∈ merkleIn f d L, f a ∈ chunks b := by
  induction d with
  | zero => intro L a ha; exact ha.elim
  | succ d ih =>
    intro L a ha
    rcases ha with ⟨i, hi, rfl⟩ | ha
    · rcases leaf_mem f d (up f L) i hi with h | ⟨b, hb, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, Or.inr hb, h⟩
    · rcases ih (up f L) a ha with h | ⟨b, hb, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, Or.inr hb, h⟩

variable {f}

/-- **Two trees of one root over an injective hash have the same leaves.** -/
theorem merkleRoot_inj {S : Set (List UInt8)} (hinj : Set.InjOn f S) (d : ℕ) :
    ∀ L L' : ℕ → Common.DigestBytes, merkleIn f d L ⊆ S → merkleIn f d L' ⊆ S →
      merkleRoot f d L = merkleRoot f d L' → ∀ i < 2 ^ d, L i = L' i := by
  induction d with
  | zero =>
    intro L L' _ _ he i hi
    obtain rfl : i = 0 := by simpa using hi
    exact he
  | succ d ih =>
    intro L L' h1 h2 he i hi
    have hup := ih (up f L) (up f L') (fun a ha ↦ h1 (Or.inr ha)) (fun a ha ↦ h2 (Or.inr ha)) he
      (i / 2) (by rw [pow_succ] at hi; omega)
    have hp := pairBytes_injective (hinj (h1 (pair_mem_merkleIn f d L (i / 2)
      (by rw [pow_succ] at hi; omega))) (h2 (pair_mem_merkleIn f d L' (i / 2)
      (by rw [pow_succ] at hi; omega))) hup)
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [show i = 2 * (i / 2) by omega]; exact hp.1
    · rw [show i = 2 * (i / 2) + 1 by omega]; exact hp.2

variable (f)

/-- The inputs a climb hashes, as a set. -/
def walkIn : ℕ → Common.DigestBytes → List Common.DigestBytes → Set (List UInt8)
  | _, _, [] => ∅
  | idx, node, s :: rest =>
    insert (if idx % 2 = 0 then pairBytes node s else pairBytes s node)
      (walkIn (idx / 2) (f (if idx % 2 = 0 then pairBytes node s else pairBytes s node)) rest)

variable {f}

/-- **A climb that reaches a tree's root over an injective hash starts at the tree's leaf.** -/
theorem walk_eq_leaf {S : Set (List UInt8)} (hinj : Set.InjOn f S) (path : List Common.DigestBytes) :
    ∀ (d : ℕ) (L : ℕ → Common.DigestBytes) (idx : ℕ) (leaf : Common.DigestBytes), path.length = d → idx < 2 ^ d →
      walkIn f idx leaf path ⊆ S → merkleIn f d L ⊆ S → walk f idx leaf path = merkleRoot f d L →
        leaf = L idx := by
  induction path with
  | nil =>
    intro d L idx leaf hd hi _ _ he
    subst hd
    obtain rfl : idx = 0 := by simpa using hi
    exact he
  | cons s rest ih =>
    intro d L idx leaf hd hi hw hm he
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp at hd; omega⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hd
    rw [walk_cons] at he
    have hlt : idx / 2 < 2 ^ d := by rw [pow_succ] at hi; omega
    have h := ih d (up f L) (idx / 2) _ hd hlt (fun a ha ↦ hw (Set.mem_insert_of_mem _ ha))
      (fun a ha ↦ hm (Or.inr ha)) he
    have hp := hinj (hw (Set.mem_insert _ _)) (hm (pair_mem_merkleIn f d L (idx / 2) hlt)) h
    rcases Nat.mod_two_eq_zero_or_one idx with h2 | h2
    · simp only [h2, ↓reduceIte] at hp
      rw [(pairBytes_injective hp).1, show 2 * (idx / 2) = idx by omega]
    · have h2' : ¬ idx % 2 = 0 := by omega
      simp only [h2', ↓reduceIte] at hp
      rw [(pairBytes_injective hp).2, show 2 * (idx / 2) + 1 = idx by omega]

/-! ## The inputs of a commitment -/

variable (f)

section Commit

variable {r : ℕ}

/-- The padded matrix's cells' bytes. -/
def cellIn (c : Fin (r * 128) → Cell) : Set (List UInt8) :=
  {a | ∃ i < nPad r, ∃ j < 128, a = cellBytes (paddedCell c i j)}

/-- The input of row `i`'s leaf: its first `64` cell digests. -/
def rowInput (c : Fin (r * 128) → Cell) (i : ℕ) : List UInt8 :=
  (List.ofFn fun j : Fin 64 ↦ cellDigest f (paddedCell c i j)).flatMap Vector.toList

/-- The rows' leaves' inputs. -/
def rowIn (c : Fin (r * 128) → Cell) : Set (List UInt8) := {a | ∃ i < nPad r, a = rowInput f c i}

/-- The root's input: `rowRoot ‖ colRoot`. -/
def rootInput (c : Fin (r * 128) → Cell) : List UInt8 := pairBytes (rowRoot f c) (colRoot f c)

/-- **The inputs a commitment hashes**: the cells', the rows' leaves', the two trees' and the
root's. -/
def commitIn (c : Fin (r * 128) → Cell) : Set (List UInt8) :=
  cellIn c ∪ rowIn f c ∪ merkleIn f (logPad r) (rowLeaves f c) ∪
    merkleIn f (7 + logPad r) (colLeaves f c) ∪ {rootInput f c}

theorem rowLeaves_eq_input (c : Fin (r * 128) → Cell) (i : ℕ) : rowLeaves f c i = f (rowInput f c i) :=
  rfl

theorem commitCells_eq (c : Fin (r * 128) → Cell) : commitCells f c = f (rootInput f c) := rfl

theorem nPad_eq : nPad r = 2 ^ logPad r := rfl

theorem two_pow_col : 2 ^ (7 + logPad r) = 128 * nPad r := by rw [pow_add]; rfl

theorem cellIn_sub (c : Fin (r * 128) → Cell) : cellIn c ⊆ commitIn f c :=
  fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inl h)))

theorem rowIn_sub (c : Fin (r * 128) → Cell) : rowIn f c ⊆ commitIn f c :=
  fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem rowTree_sub (c : Fin (r * 128) → Cell) :
    merkleIn f (logPad r) (rowLeaves f c) ⊆ commitIn f c :=
  fun _ h ↦ Or.inl (Or.inl (Or.inr h))

theorem colTree_sub (c : Fin (r * 128) → Cell) :
    merkleIn f (7 + logPad r) (colLeaves f c) ⊆ commitIn f c :=
  fun _ h ↦ Or.inl (Or.inr h)

theorem rootInput_mem (c : Fin (r * 128) → Cell) : rootInput f c ∈ commitIn f c :=
  Or.inr rfl

theorem colIdx_mod {i j : ℕ} (hi : i < nPad r) : (j * nPad r + i) % nPad r = i := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem colIdx_div {i j : ℕ} (hi : i < nPad r) : (j * nPad r + i) / nPad r = j := by
  have hpos : 0 < nPad r := by unfold nPad; positivity
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hi, Nat.zero_add]

theorem colLeaves_eq_cell (c : Fin (r * 128) → Cell) (i j : ℕ) (hi : i < nPad r) :
    colLeaves f c (j * nPad r + i) = f (cellBytes (paddedCell c i j)) := by
  simp only [colLeaves, cellDigest, colIdx_mod hi, colIdx_div hi]

theorem colLeaves_mem (c : Fin (r * 128) → Cell) (l : ℕ) (hl : l < 2 ^ (7 + logPad r)) :
    cellBytes (paddedCell c (l % nPad r) (l / nPad r)) ∈ cellIn c := by
  have hpos : 0 < nPad r := by unfold nPad; positivity
  rw [two_pow_col] at hl
  exact ⟨_, Nat.mod_lt _ hpos, _, by rw [Nat.div_lt_iff_lt_mul hpos]; omega, rfl⟩

/-- **The commitment depends on the hash only on its inputs.** -/
theorem commitIn_congr (f' : List UInt8 → Common.DigestBytes) (c : Fin (r * 128) → Cell)
    (h : ∀ a ∈ commitIn f c, f a = f' a) :
    commitIn f' c = commitIn f c ∧ commitCells f' c = commitCells f c := by
  have hcell : ∀ i < nPad r, ∀ j < 128,
      f (cellBytes (paddedCell c i j)) = f' (cellBytes (paddedCell c i j)) :=
    fun i hi j hj ↦ h _ (cellIn_sub f c ⟨i, hi, j, hj, rfl⟩)
  have hrowIn : ∀ i < nPad r, rowInput f c i = rowInput f' c i := fun i hi ↦ by
    simp only [rowInput, cellDigest]
    congr 1
    exact List.ofFn_inj.mpr (funext fun j ↦ hcell i hi j (by omega))
  have hrowIn' : rowIn f' c = rowIn f c := by
    ext a
    simp only [rowIn, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, (hrowIn i hi).symm⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, hrowIn i hi⟩
  have hrow := merkleIn_congr f f' (logPad r) (rowLeaves f c) (rowLeaves f' c)
    (fun i hi ↦ by
      rw [rowLeaves_eq_input, rowLeaves_eq_input, ← hrowIn i hi]
      exact h _ (rowIn_sub f c ⟨i, hi, rfl⟩))
    fun a ha ↦ h a (rowTree_sub f c ha)
  have hcol := merkleIn_congr f f' (7 + logPad r) (colLeaves f c) (colLeaves f' c)
    (fun l hl ↦ by
      have hm := colLeaves_mem c l hl
      simp only [colLeaves, cellDigest]
      exact h _ (cellIn_sub f c hm))
    fun a ha ↦ h a (colTree_sub f c ha)
  have hroot : rootInput f' c = rootInput f c := by
    simp only [rootInput, rowRoot, colRoot, hrow.2, hcol.2]
  refine ⟨?_, ?_⟩
  · simp only [commitIn, hrowIn', hrow.1, hcol.1, hroot]
  · rw [commitCells_eq, commitCells_eq, hroot]
    exact (h _ (rootInput_mem f c)).symm

theorem rowRoot_mem_chunks (c : Fin (r * 128) → Cell) : rowRoot f c ∈ chunks (rootInput f c) :=
  mem_chunks_pairBytes_left _ _

theorem colRoot_mem_chunks (c : Fin (r * 128) → Cell) : colRoot f c ∈ chunks (rootInput f c) :=
  mem_chunks_pairBytes_right _ _

/-- **Every input of a commitment but the root's hashes to a digest one of its inputs carries.** -/
theorem commitIn_parent (c : Fin (r * 128) → Cell) (a : List UInt8) (ha : a ∈ commitIn f c) :
    f a = commitCells f c ∨ ∃ b ∈ commitIn f c, f a ∈ chunks b := by
  have hrowT : ∀ v, (v = merkleRoot f (logPad r) (rowLeaves f c) ∨
      ∃ b ∈ merkleIn f (logPad r) (rowLeaves f c), v ∈ chunks b) →
        ∃ b ∈ commitIn f c, v ∈ chunks b := by
    rintro v (rfl | ⟨b, hb, h⟩)
    · exact ⟨_, rootInput_mem f c, rowRoot_mem_chunks f c⟩
    · exact ⟨b, rowTree_sub f c hb, h⟩
  have hcolT : ∀ v, (v = merkleRoot f (7 + logPad r) (colLeaves f c) ∨
      ∃ b ∈ merkleIn f (7 + logPad r) (colLeaves f c), v ∈ chunks b) →
        ∃ b ∈ commitIn f c, v ∈ chunks b := by
    rintro v (rfl | ⟨b, hb, h⟩)
    · exact ⟨_, rootInput_mem f c, colRoot_mem_chunks f c⟩
    · exact ⟨b, colTree_sub f c hb, h⟩
  rcases ha with (((⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, rfl⟩) | ha) | ha) | ha
  · refine Or.inr (hcolT _ ?_)
    rw [← colLeaves_eq_cell f c i j hi]
    refine leaf_mem f _ _ _ ?_
    rw [two_pow_col]
    nlinarith
  · refine Or.inr (hrowT _ ?_)
    rw [← rowLeaves_eq_input f c i]
    exact leaf_mem f _ _ _ hi
  · rcases merkleIn_parent f _ _ a ha with h | h
    · exact Or.inr (hrowT _ (Or.inl h))
    · exact Or.inr (hrowT _ (Or.inr h))
  · rcases merkleIn_parent f _ _ a ha with h | h
    · exact Or.inr (hcolT _ (Or.inl h))
    · exact Or.inr (hcolT _ (Or.inr h))
  · rw [Set.mem_singleton_iff.mp ha]
    exact Or.inl rfl

variable {f}

theorem paddedCell_pos (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    paddedCell c (posRow p) (posCell p) = c p := by
  have h1 : (posRow p : ℕ) < r := (posRow p).isLt
  have h2 : (posCell p : ℕ) < 128 := (posCell p).isLt
  simp only [paddedCell, h1, h2, and_self, ↓reduceDIte]
  congr 1
  apply Fin.ext
  simp only [pos, posRow, posCell]
  omega

/-- **One root, one matrix**, over a hash injective on a set holding both commitments' inputs. -/
theorem commit_unique {S : Set (List UInt8)} (hinj : Set.InjOn f S) {c c' : Fin (r * 128) → Cell}
    (h1 : commitIn f c ⊆ S) (h2 : commitIn f c' ⊆ S) (he : commitCells f c = commitCells f c') :
    c = c' := by
  have hp := pairBytes_injective (hinj (h1 (rootInput_mem f c)) (h2 (rootInput_mem f c')) he)
  have hl := merkleRoot_inj hinj (7 + logPad r) _ _ (fun a ha ↦ h1 (colTree_sub f c ha))
    (fun a ha ↦ h2 (colTree_sub f c' ha)) hp.2
  funext p
  have hrow : (posRow p : ℕ) < nPad r := lt_of_lt_of_le (posRow p).isLt (le_nPad r)
  have hidx : (posCell p : ℕ) * nPad r + posRow p < 2 ^ (7 + logPad r) := by
    have := (posCell p).isLt
    rw [two_pow_col]
    nlinarith
  have h := hl _ hidx
  rw [colLeaves_eq_cell f c _ _ hrow, colLeaves_eq_cell f c' _ _ hrow] at h
  have hc := cellBytes_injective (hinj (h1 (cellIn_sub f c ⟨_, hrow, _, (posCell p).isLt, rfl⟩))
    (h2 (cellIn_sub f c' ⟨_, hrow, _, (posCell p).isLt, rfl⟩)) h)
  rwa [paddedCell_pos, paddedCell_pos] at hc

variable (f)

/-- **The inputs an opening's check hashes**: the cell's bytes, the climb's and the root's. -/
def verifyIn (p : Fin (r * 128)) (x : Cell) (τ : Opening) : Set (List UInt8) :=
  insert (cellBytes x) (insert (pairBytes τ.rowRoot (walk f (colIndex p) (cellDigest f x) τ.path))
    (walkIn f (colIndex p) (cellDigest f x) τ.path))

variable {f}

/-- **An opening that verifies against a matrix's root opens the matrix's cell**, over a hash
injective on a set holding the commitment's and the check's inputs. -/
theorem verifyCell_agree {S : Set (List UInt8)} (hinj : Set.InjOn f S)
    {c : Fin (r * 128) → Cell} {p : Fin (r * 128)} {x : Cell} {τ : Opening}
    (hc : commitIn f c ⊆ S) (hv : verifyIn f p x τ ⊆ S)
    (hver : verifyCell f r (commitCells f c) p x τ = true) : x = c p := by
  simp only [verifyCell, Bool.and_eq_true, decide_eq_true_eq] at hver
  obtain ⟨hlen, hroot⟩ := hver
  have hp := pairBytes_injective (hinj (hv (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    (hc (rootInput_mem f c)) hroot)
  have hleaf := walk_eq_leaf hinj τ.path (7 + logPad r) (colLeaves f c) (colIndex p)
    (cellDigest f x) hlen (colIndex_lt p)
    (fun a ha ↦ hv (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ha)))
    (fun a ha ↦ hc (colTree_sub f c ha)) hp.2
  have hrow : (posRow p : ℕ) < nPad r := lt_of_lt_of_le (posRow p).isLt (le_nPad r)
  rw [show colIndex p = (posCell p : ℕ) * nPad r + posRow p from rfl,
    colLeaves_eq_cell f c _ _ hrow] at hleaf
  have hx := cellBytes_injective (hinj (hv (Set.mem_insert _ _))
    (hc (cellIn_sub f c ⟨_, hrow, _, (posCell p).isLt, rfl⟩)) hleaf)
  rwa [paddedCell_pos] at hx

end Commit

/-! ## Over a partial hash -/

section Partial

variable {g : List UInt8 → Option Common.DigestBytes} (hg : ∀ a u, g a = some u → u = f a)
include hg

theorem upM_some (Lm : ℕ → Option Common.DigestBytes) (L : ℕ → Common.DigestBytes) (hL : ∀ i u, Lm i = some u → u = L i)
    (i : ℕ) (v : Common.DigestBytes) (hv : upM g Lm i = some v) :
    v = up f L i ∧ Lm (2 * i) ≠ none ∧ Lm (2 * i + 1) ≠ none ∧
      g (pairBytes (L (2 * i)) (L (2 * i + 1))) ≠ none := by
  simp only [upM, Option.bind_eq_bind', Option.bind_eq_some_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  rw [hL _ _ ha, hL _ _ hb] at hab
  exact ⟨hg _ _ hab, by simp [ha], by simp [hb], by simp [hab]⟩

theorem merkleRootM_some (d : ℕ) :
    ∀ (Lm : ℕ → Option Common.DigestBytes) (L : ℕ → Common.DigestBytes), (∀ i u, Lm i = some u → u = L i) →
      ∀ v, merkleRootM g d Lm = some v →
        v = merkleRoot f d L ∧ (∀ i < 2 ^ d, Lm i ≠ none) ∧ ∀ a ∈ merkleIn f d L, g a ≠ none := by
  induction d with
  | zero =>
    intro Lm L hL v hv
    refine ⟨hL 0 v hv, fun i hi ↦ ?_, fun a ha ↦ ha.elim⟩
    obtain rfl : i = 0 := by simpa using hi
    change Lm 0 = some v at hv
    rw [hv]
    simp
  | succ d ih =>
    intro Lm L hL v hv
    have hL' : ∀ i u, upM g Lm i = some u → u = up f L i :=
      fun i u hu ↦ (upM_some f hg Lm L hL i u hu).1
    obtain ⟨h1, h2, h3⟩ := ih (upM g Lm) (up f L) hL' v hv
    have hup : ∀ i < 2 ^ d, ∃ u, upM g Lm i = some u := fun i hi ↦
      Option.ne_none_iff_exists'.mp (h2 i hi)
    refine ⟨h1, fun i hi ↦ ?_, fun a ha ↦ ?_⟩
    · obtain ⟨u, hu⟩ := hup (i / 2) (by rw [pow_succ] at hi; omega)
      obtain ⟨-, ha, hb, -⟩ := upM_some f hg Lm L hL _ u hu
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · rwa [show 2 * (i / 2) = i by omega] at ha
      · rwa [show 2 * (i / 2) + 1 = i by omega] at hb
    · rcases ha with ⟨i, hi, rfl⟩ | ha
      · obtain ⟨u, hu⟩ := hup i hi
        exact (upM_some f hg Lm L hL _ u hu).2.2.2
      · exact h3 a ha

theorem mapM_some {β : Type} (F : β → Option Common.DigestBytes) (F' : β → Common.DigestBytes)
    (hF : ∀ b u, F b = some u → u = F' b) (l : List β) (ds : List Common.DigestBytes)
    (h : l.mapM F = some ds) : ds = l.map F' ∧ ∀ b ∈ l, F b ≠ none := by
  induction l generalizing ds with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    exact ⟨h.symm, by simp⟩
  | cons b l ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind', Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨u, hu, ds', hds', rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih ds' hds'
    refine ⟨by rw [h1, hF _ _ hu]; rfl, fun b' hb' ↦ ?_⟩
    rcases List.mem_cons.mp hb' with rfl | hb'
    · simp [hu]
    · exact h2 b' hb'

/-- **A commitment over a partial hash that returns** returns the pure commitment, its inputs in
the hash's domain. -/
theorem commitCellsM_some {r : ℕ} (c : Fin (r * 128) → Cell) (v : Common.DigestBytes)
    (hv : commitCellsM g c = some v) :
    v = commitCells f c ∧ ∀ a ∈ commitIn f c, g a ≠ none := by
  simp only [commitCellsM, Option.bind_eq_bind', Option.bind_eq_some_iff] at hv
  obtain ⟨ra, hra, ca, hca, hroot⟩ := hv
  -- the row leaves
  have hrowM : ∀ i u, rowLeavesM g c i = some u → u = rowLeaves f c i ∧
      (∀ j < 64, g (cellBytes (paddedCell c i j)) ≠ none) ∧ g (rowInput f c i) ≠ none := by
    intro i u hu
    simp only [rowLeavesM, Option.bind_eq_bind', Option.bind_eq_some_iff] at hu
    obtain ⟨ds, hds, hu⟩ := hu
    obtain ⟨h1, h2⟩ := mapM_some f hg (β := ℕ) (fun j : ℕ ↦ g (cellBytes (paddedCell c i j)))
      (fun j : ℕ ↦ cellDigest f (paddedCell c i j)) (fun j u hu ↦ hg _ _ hu) _ ds hds
    have hin : ds.flatMap Vector.toList = rowInput f c i := by
      rw [h1, rowInput, ofFn_val_eq_map_range (g := fun j ↦ cellDigest f (paddedCell c i j))]
    rw [hin] at hu
    exact ⟨hg _ _ hu, fun j hj ↦ h2 j (List.mem_range.mpr hj), by simp [hu]⟩
  obtain ⟨hra', hrl, hrin⟩ := merkleRootM_some f hg (logPad r) (rowLeavesM g c) (rowLeaves f c)
    (fun i u hu ↦ (hrowM i u hu).1) ra hra
  obtain ⟨hca', hcl, hcin⟩ := merkleRootM_some f hg (7 + logPad r) (colLeavesM g c)
    (colLeaves f c) (fun l u hu ↦ hg _ _ hu) ca hca
  rw [hra', hca'] at hroot
  refine ⟨hg _ _ hroot, fun a ha ↦ ?_⟩
  rcases ha with (((⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, rfl⟩) | ha) | ha) | ha
  · have hidx : j * nPad r + i < 2 ^ (7 + logPad r) := by rw [two_pow_col]; nlinarith
    have h := hcl _ hidx
    simp only [colLeavesM] at h
    rwa [colIdx_mod hi, colIdx_div hi] at h
  · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp (hrl i hi)
    exact (hrowM i u hu).2.2
  · exact hrin a ha
  · exact hcin a ha
  · rw [Set.mem_singleton_iff.mp ha]
    simp [rootInput, rowRoot, colRoot, hroot]

theorem walkM_some (path : List Common.DigestBytes) :
    ∀ (idx : ℕ) (node v : Common.DigestBytes), walkM g idx node path = some v →
      v = walk f idx node path ∧ ∀ a ∈ walkIn f idx node path, g a ≠ none := by
  induction path with
  | nil =>
    intro idx node v hv
    simp only [walkM, Option.pure_def, Option.some.injEq] at hv
    exact ⟨hv.symm, fun a ha ↦ ha.elim⟩
  | cons s rest ih =>
    intro idx node v hv
    simp only [walkM, Option.bind_eq_bind', Option.bind_eq_some_iff] at hv
    obtain ⟨u, hu, hv⟩ := hv
    have hu' : u = f (if idx % 2 = 0 then pairBytes node s else pairBytes s node) := hg _ _ hu
    obtain ⟨h1, h2⟩ := ih _ u v hv
    rw [hu'] at h1 h2
    refine ⟨by rw [walk_cons]; exact h1, fun a ha ↦ ?_⟩
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · simp [hu]
    · exact h2 a ha

/-- **An opening's check over a partial hash that returns** returns the pure check, its inputs
in the hash's domain. -/
theorem verifyCellM_some {r : ℕ} (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : Opening)
    (b : Bool) (hb : verifyCellM g r com p x τ = some b) :
    b = verifyCell f r com p x τ ∧ ∀ a ∈ verifyIn f p x τ, g a ≠ none := by
  simp only [verifyCellM, Option.bind_eq_bind', Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at hb
  obtain ⟨d, hd, w, hw, root, hroot, rfl⟩ := hb
  have hd' : d = cellDigest f x := hg _ _ hd
  subst hd'
  obtain ⟨hw1, hw2⟩ := walkM_some f hg τ.path _ _ w hw
  subst hw1
  have hroot' := hg _ _ hroot
  subst hroot'
  refine ⟨rfl, fun a ha ↦ ?_⟩
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · simp [cellDigest] at hd; simp [hd]
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · simp [hroot]
  · exact hw2 a ha

end Partial

end LeanDa
