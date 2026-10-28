/-
  LeanVM.Guest.B1.Da.VerifyMath

  From the digests `da_verify` computes, a witness that opens its claim (`Da.Witness.Opens`).
-/

module

public import LeanVM.Guest.B1.Da.Tree

/-!
# The claim `da_verify` returns is opened

Given `r` rows (`1 ≤ r ≤ 1024`, padded to `2^L = LeanDa.nPad r`), the symbols of cell `(i, j)`
(`syms i j`, `256`) and the weights of column `j` (`ws j`, `256`), with every row orthogonal to
the weights (`Σ_j Σ_e ws j e · sym i j e = 0`), `opens_of` builds the witness: the rows the cells
concatenate, the vector the columns concatenate. It opens the root `daRoot` (the hash of the row
tree's root and the column tree's, over the cell digests `cellD`, the row digests `rowD` and
LeanDA's padding digests) and the vector digest `daVd` (the hash of the column digests `colD`):
LeanDA's commitment (`LeanDa.commitCodewords`, Benedikt Wagner's LeanDA as `lean_da` transcribes
the crate) is computed level by level (`treeRoot_range`), its column tree split into the column
roots (`merkleRoot_add`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-! ## Blocks of a list -/

theorem flatMap_getD {α : Type} (f : ℕ → List α) (m : ℕ) (hf : ∀ j, (f j).length = m) (d : α) :
    ∀ n j e, j < n → e < m → ((List.range n).flatMap f).getD (m * j + e) d = (f j).getD e d
  | 0, _, _, h, _ => absurd h (by omega)
  | n + 1, j, e, hj, he => by
    have hl : ((List.range n).flatMap f).length = m * n := by
      simp [List.length_flatMap, hf, mul_comm]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_ge j n with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hl]; nlinarith), flatMap_getD f m hf d n j e h he]
    · obtain rfl : j = n := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl,
        show m * j + e - m * j = e by omega]

theorem length_flatMap_range {α : Type} (f : ℕ → List α) (m n : ℕ) (hf : ∀ j, (f j).length = m) :
    ((List.range n).flatMap f).length = n * m := by
  simp [List.length_flatMap, hf]

/-- Block `j` of a list of blocks of `m`. -/
theorem block_eq {α : Type} [Inhabited α] (f : ℕ → List α) (m : ℕ) (hf : ∀ j, (f j).length = m)
    {n j : ℕ} (hj : j < n) (d : α) : ((((List.range n).flatMap f).drop (j * m)).take m) = f j := by
  have hl := length_flatMap_range f m n hf
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, hl, hf]
    have : m ≤ n * m - j * m := by
      rw [← Nat.sub_mul]; exact Nat.le_mul_of_pos_left m (by omega)
    omega
  · intro e h1 h2
    rw [hf] at h2
    rw [List.getElem_take, List.getElem_drop]
    have := flatMap_getD f m hf d n j e hj h2
    have hk : j * m + e < ((List.range n).flatMap f).length := by rw [hl]; nlinarith
    rw [← List.getD_eq_getElem _ d hk, show j * m + e = m * j + e by ring, this,
      List.getD_eq_getElem _ _ (by rw [hf]; exact h2)]

theorem merkleRoot_congr (H : List UInt8 → Common.KDigest) :
    ∀ (d : ℕ) {f g : ℕ → Common.KDigest}, (∀ i < 2 ^ d, f i = g i) →
      LeanDa.merkleRoot H d f = LeanDa.merkleRoot H d g
  | 0, f, g, h => h 0 (by norm_num)
  | d + 1, f, g, h => by
    rw [LeanDa.merkleRoot, LeanDa.merkleRoot]
    refine merkleRoot_congr H d fun i hi => ?_
    simp only [LeanDa.up]
    rw [h (2 * i) (by rw [pow_succ]; omega), h (2 * i + 1) (by rw [pow_succ]; omega)]

/-! ## The digests -/

section
variable (r L : ℕ) (syms : ℕ → ℕ → List K) (ws : ℕ → List E)

/-- Cell `(i, j)`'s digest. -/
def cellD (i j : ℕ) : Digest := keccak256 ((syms i j).flatMap kBytes)

/-- Row `i`'s digest: the hash of its `64` payload cells' digests. -/
def rowD (i : ℕ) : Digest := keccak256 ((List.range 64).flatMap fun j => digestBytes (cellD syms i j))

/-- Column `j`'s digest. -/
def colD (j : ℕ) : Digest := keccak256 ((ws j).flatMap Node.eBytes)

/-- The row tree's leaves: the rows' digests, then the padding row's. -/
def rowLeaf (i : ℕ) : Digest := if i < r then rowD syms i else daPadRowDigest

/-- Column `j`'s leaves: the cells' digests, then the padding cell's. -/
def cellLeaf (j i : ℕ) : Digest := if i < r then cellD syms i j else daPadCellDigest

/-- **The root**: the hash of the row tree's root and the column tree's. -/
def daRoot : Digest :=
  keccak256 (digestBytes (mRoot L (rowLeaf r syms)) ++
    digestBytes (mRoot 7 fun j => mRoot L (cellLeaf r syms j)))

/-- **The vector's digest**: the hash of the columns' digests. -/
def daVd : Digest := keccak256 ((List.range 128).flatMap fun j => digestBytes (colD ws j))

/-- The rows. -/
def daRows : List (List K) := (List.range r).map fun i => (List.range 128).flatMap (syms i)

/-- The vector. -/
def daVector : List E := (List.range 128).flatMap ws

end

/-! ## The witness -/

theorem keccak_eq (l : List UInt8) : LeanVM.Da.keccak l = LeanVM.Protocol.Digest.toBytes (keccak256 l) := rfl

theorem sum_range_mul (g : ℕ → E) (m : ℕ) : ∀ n,
    ∑ b ∈ Finset.range (n * m), g b = ∑ j ∈ Finset.range n, ∑ e ∈ Finset.range m, g (m * j + e)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul g m n, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_comm m n]

/-- **The witness opens the claim.** -/
theorem opens_of {r L : ℕ} {syms : ℕ → ℕ → List K} {ws : ℕ → List E} (hr1 : 1 ≤ r)
    (hr : r ≤ LeanDa.maxRows) (hL : LeanDa.nPad r = 2 ^ L) (hrL : r ≤ 2 ^ L)
    (hsyms : ∀ i j, (syms i j).length = 256) (hws : ∀ j, (ws j).length = 256)
    (hdot : ∀ i < r, ∑ j ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      (ws j).getD e 0 * ofK ((syms i j).getD e 0) = 0) :
    (⟨daRows r syms, daVector ws⟩ : LeanVM.Da.Witness).Opens (daRoot r L syms) (daVd ws) := by
  have hrow : ∀ i, ((List.range 128).flatMap (syms i)).length = 2 ^ LeanDa.logM := fun i => by
    rw [length_flatMap_range _ 256 _ (hsyms i)]; rfl
  have hcell : ∀ i, ∀ j < 128, LeanDa.listCell ((List.range 128).flatMap (syms i)) j = syms i j :=
    fun i j hj => block_eq (syms i) 256 (hsyms i) hj 0
  have hlcd : ∀ i, ∀ j < 128, LeanDa.listCellDigest LeanVM.Da.keccak
      ((List.range 128).flatMap (syms i)) j = LeanVM.Protocol.Digest.toBytes (cellD syms i j) := fun i j hj => by
    rw [LeanDa.listCellDigest, hcell i j hj, keccak_eq, cellD, show LeanDa.kBytes = kBytes from
      funext kBytes_eq]
  have hlen : (daRows r syms).length = r := by simp [daRows]
  -- the row tree
  have hrd : ∀ i (hi : i < r), LeanDa.rowDigest LeanVM.Da.keccak
      ((daRows r syms)[i]'(by rw [hlen]; exact hi)) = LeanVM.Protocol.Digest.toBytes (rowD syms i) := by
    intro i hi
    have : (daRows r syms)[i]'(by rw [hlen]; exact hi) = (List.range 128).flatMap (syms i) := by
      simp [daRows]
    rw [this, LeanDa.rowDigest, keccak_eq, rowD]
    congr 2
    refine List.flatMap_congr fun j hj => ?_
    have hj' : j < 64 := by simpa [LeanDa.payloadCells] using List.mem_range.mp hj
    rw [hlcd i j (by omega), toList_toBytes]
  have hRow : LeanDa.treeRoot LeanVM.Da.keccak ((daRows r syms).map
      (LeanDa.rowDigest LeanVM.Da.keccak) ++ List.replicate
        (LeanDa.nPad (daRows r syms).length - (daRows r syms).length)
        (LeanDa.paddingRow LeanVM.Da.keccak)) = LeanVM.Protocol.Digest.toBytes (mRoot L (rowLeaf r syms)) := by
    rw [hlen, hL, toBytes_mRoot, ← treeRoot_range]
    congr 1
    refine List.ext_getElem (by simp [hlen]; omega) fun i h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h2
    rw [List.getElem_map, List.getElem_range, Function.comp_apply, rowLeaf]
    by_cases hi : i < r
    · rw [List.getElem_append_left (by simp [hlen, hi]), List.getElem_map, ite_pos' hi, ← hrd i hi]
    · rw [List.getElem_append_right (by simp [hlen]; omega), List.getElem_replicate, ite_neg' hi,
        paddingRow_eq]
  -- the column tree
  have hCol : LeanDa.treeRoot LeanVM.Da.keccak ((List.range LeanDa.cellsPerRow).flatMap fun j =>
      (List.range (LeanDa.nPad (daRows r syms).length)).map fun i => if h : i < (daRows r syms).length then
        LeanDa.listCellDigest LeanVM.Da.keccak (daRows r syms)[i] j
      else LeanDa.paddingCell LeanVM.Da.keccak) =
      LeanVM.Protocol.Digest.toBytes (mRoot 7 fun j => mRoot L (cellLeaf r syms j)) := by
    rw [show LeanDa.nPad (daRows r syms).length = 2 ^ L by rw [hlen, hL]]
    have e1 : ((List.range LeanDa.cellsPerRow).flatMap fun j =>
        (List.range (2 ^ L)).map fun i => if h : i < (daRows r syms).length then
          LeanDa.listCellDigest LeanVM.Da.keccak (daRows r syms)[i] j
        else LeanDa.paddingCell LeanVM.Da.keccak) =
        (List.range 128).flatMap fun j => (List.range (2 ^ L)).map fun i =>
          LeanVM.Protocol.Digest.toBytes (cellLeaf r syms j i) := by
      refine List.flatMap_congr fun j hj => List.map_congr_left fun i _ => ?_
      have hj' : j < 128 := List.mem_range.mp hj
      rw [cellLeaf]
      split
      · rename_i hi
        rw [hlen] at hi
        rw [ite_pos' hi, ← hlcd i j hj']
        simp [daRows]
      · rename_i hi
        rw [hlen] at hi
        rw [ite_neg' hi, paddingCell_eq]
    rw [e1, flatMap_range_range 128 (2 ^ L) (by positivity),
      show 128 * 2 ^ L = 2 ^ (7 + L) by rw [pow_add]; norm_num, treeRoot_range, merkleRoot_add,
      toBytes_mRoot]
    congr 1
    funext j
    rw [Function.comp_apply, toBytes_mRoot]
    refine merkleRoot_congr _ L fun i hi => ?_
    simp only [Function.comp_apply]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hi, Nat.zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  refine ⟨by rw [hlen]; exact hr1, by rw [hlen]; exact hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro row hrow'
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hrow'
    exact hrow i
  · -- the commitment
    simp only [LeanDa.commitCodewords]
    rw [hRow, hCol, keccak_pair]
    rfl
  · rw [daVector, length_flatMap_range _ 256 _ hws]; rfl
  · -- the vector's digest
    rw [LeanDa.vectorDigest, keccak_eq, daVd]
    congr 2
    refine List.flatMap_congr fun j hj => ?_
    have hj' : j < 128 := List.mem_range.mp hj
    rw [LeanDa.columnDigest, show LeanDa.cellSymbols = 256 from rfl, daVector,
      block_eq ws 256 hws hj' 0, limbBytes_eq, keccak_eq, toList_toBytes]
    rfl
  · -- orthogonality
    intro row hrow'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow'
    have hi' := List.mem_range.mp hi
    rw [LeanDa.dot, Fin.sum_univ_eq_sum_range (fun b => (daVector ws).getD b 0 *
      LeanDa.ι (((List.range 128).flatMap (syms i)).getD b 0)) (2 ^ 15),
      show 2 ^ 15 = 128 * 256 by norm_num, sum_range_mul _ 256 128]
    refine (Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun e he => ?_).trans (hdot i hi')
    have hj' := Finset.mem_range.mp hj
    have he' := Finset.mem_range.mp he
    rw [daVector, flatMap_getD ws 256 hws 0 128 j e hj' he',
      flatMap_getD (syms i) 256 (hsyms i) 0 128 j e hj' he']
    rfl

end
end LeanVM.Guest.B1.Da
