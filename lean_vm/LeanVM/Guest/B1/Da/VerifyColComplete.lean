/-
  LeanVM.Guest.B1.Da.VerifyColComplete

  `da_verify`'s columns, completely: each column on the honest memory.
-/

module

public import LeanVM.Guest.B1.Da.VerifyCDefs
public import LeanVM.Guest.B1.Da.ColumnComplete
public import LeanVM.Guest.B1.Da.CellComplete
public import LeanVM.Guest.B1.Da.VectorComplete
public import LeanVM.Guest.B1.Da.VerifyHelp

/-!
# `da_verify`'s columns, completely

`dv_col`: on the honest memory (`DaMem`), column `j < 128` holds at the words `da_verify`'s column
loops hand it: its vector check (`da_vector_cell_complete`), every row's cell check
(`da_verify_cell_complete`) with the running sum's step and the cell's words at the node (and in
the prefix for `j < 64`), every padding row, its tree's root (`da_levels_complete`) and the root in
the column tree.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

/-! ## Reading the honest memory -/

theorem gen_sq (j : ℕ) : gen ^ j * gen ^ j = gen ^ (2 * j) := by rw [← pow_add, two_mul]

/-- A block of two in a run of blocks of two. -/
theorem reads_pair {p : E} {n : ℕ} {f : ℕ → List E} (h : ReadsAt rd p ((List.range n).flatMap f))
    (hf : ∀ j, (f j).length = 2) {j : ℕ} (hj : j < n) {k : ℕ} (hk : k < 2) :
    LoadHolds rd (p * gen ^ (2 * j)) k ((f j).getD k 0) := by
  have hl := length_flatMap_range f 2 n hf
  have e := flatMap_getD f 2 hf 0 n j k hj hk
  rw [loadHolds_mul_gen_pow, ← e, List.getD_eq_getElem _ _ (by rw [hl]; nlinarith)]
  exact h _ _

/-- A leaf of a tree in memory. -/
theorem treeMem_leaf {tree : E} {k : ℕ} {leaves : List (E × E)} (h : TreeMem rd tree k leaves)
    (hlen : leaves.length = 2 ^ k) {i : ℕ} (hi : i < 2 ^ k) :
    LoadHolds rd (tree * gen ^ (2 * i)) 0 (leaves.getD i 0).1 ∧
      LoadHolds rd (tree * gen ^ (2 * i)) 1 (leaves.getD i 0).2 := by
  obtain ⟨q0, q1⟩ := pairCells_getD' leaves i
  have l0 := treeMem_load hlen h (l := 0) (Nat.zero_le _) (i := 2 * i) (by simp; omega)
  have l1 := treeMem_load hlen h (l := 0) (Nat.zero_le _) (i := 2 * i + 1) (by simp; omega)
  simp only [off_zero, pow_zero, mul_one, treeLvl, Function.iterate_zero, id] at l0 l1
  rw [q0] at l0
  rw [q1] at l1
  rw [loadHolds_mul_gen_pow, Nat.add_zero]
  refine ⟨l0, ?_⟩
  rw [loadHolds_mul_gen_pow]
  exact l1

theorem length_nodeLeaves (r L : ℕ) (syms : ℕ → ℕ → List K) (j : ℕ) :
    (nodeLeaves r L syms j).length = 2 ^ L := by simp [nodeLeaves]

theorem nodeLeaves_getD (r L : ℕ) (syms : ℕ → ℕ → List K) (j : ℕ) {i : ℕ} (hi : i < 2 ^ L) :
    (nodeLeaves r L syms j).getD i 0 = digestScalars (cellLeaf r syms j i) := by
  simp [nodeLeaves, List.getD_eq_getElem?_getD, hi]

theorem canon_scalars_map {α : Type} (f : α → Digest) (l : List α) :
    AllCanonical (pairCells (l.map fun i => digestScalars (f i))) := by
  intro c hc
  simp only [pairCells, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨_, ⟨a, -, rfl⟩, hc⟩ := hc
  set d := f a
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact (digestScalars_canonical d).1
  · exact (digestScalars_canonical d).2

theorem canon_nodeLeaves (r L : ℕ) (syms : ℕ → ℕ → List K) (j : ℕ) :
    AllCanonical (pairCells (nodeLeaves r L syms j)) := by
  exact canon_scalars_map _ _

/-! ## A column -/

variable {r L : ℕ} {syms : ℕ → ℕ → List K} {ws : ℕ → List E}

set_option maxHeartbeats 1000000 in
/-- **Column `j` holds** on the honest memory. -/
theorem dv_col {P : DaPtrs} (hm : DaMem r L syms ws rd P) (hL : L ≤ 10) (hrL : r ≤ 2 ^ L)
    (hsl : ∀ i j, (syms i j).length = 256) (hwl : ∀ j, (ws j).length = 256) {j : ℕ}
    (hj : j < 128) :
    coreProgram.Rel rd (if j < 64 then "da_verify_column__L1" else "da_verify_column__L0")
      [gen ^ j, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct, P.rb, P.cd] [] := by
  have hgr : 2 ^ L - r + r = 2 ^ L := by omega
  -- the vector check
  have hvec : coreProgram.Rel rd "da_vector_cell" [P.cd * (gen ^ j * gen ^ j)] [P.lv j] := by
    refine da_vector_cell_complete rd _ _ (ws j) (by simp [LeanDa.cellSymbols, hwl]) (hm.lvK j hj)
      (fun k hk v hv => ?_) (fun k hk => ?_)
    · have l := hm.lv j hj k (by rw [hwl]; simpa [LeanDa.cellSymbols] using hk)
      have := l.2
      rw [hv] at this
      rw [List.getD_eq_getElem _ _ (by rw [hwl]; simpa [LeanDa.cellSymbols] using hk)]
      exact Option.some.inj this
    · have hk2 : k < 2 := by simpa [digestCells] using hk
      have := reads_pair hm.cd (f := fun j => digestCells (colD ws j)) (fun _ => rfl) hj hk2
      rw [← List.getD_eq_getElem _ 0 hk, gen_sq]
      exact this
  -- the rows
  have hcellR : ∀ i < r, coreProgram.Rel rd "da_verify_cell" [P.lv j]
      [(digestScalars (cellD syms i j)).1, (digestScalars (cellD syms i j)).2, cellDot syms ws i j] := by
    intro i hi
    have := da_verify_cell_complete rd (P.lv j) (syms i j) (ws j) (by simp [LeanDa.cellSymbols, hsl])
      (by simp [LeanDa.cellSymbols, hwl]) (hm.lv j hj)
    rw [cellRets, digestCells] at this
    rwa [show ((List.range LeanDa.cellSymbols).map fun e ↦ (ws j).getD e 0 * ofK ((syms i j).getD e 0)).sum
      = cellDot syms ws i j by rw [cellDot, list_sum_range]; rfl] at this
  have hacc : ∀ i < r, ∀ b ≤ 128, LoadHolds rd (P.acc * (gen ^ i) ^ 129 * gen ^ j) (b - j)
      (accSum syms ws i b) ∨ b < j := by
    intro i hi b hb
    by_cases hbj : b < j
    · exact Or.inr hbj
    · refine Or.inl ?_
      rw [loadHolds_mul_gen_pow, show j + (b - j) = b by omega]
      have := hm.acc i hi b (by simp; omega)
      simpa using this
  have hrow : ∀ i < r, (coreProgram.Rel rd "da_verify_cell" [P.lv j]
      [(digestScalars (cellD syms i j)).1, (digestScalars (cellD syms i j)).2, cellDot syms ws i j]) ∧
      LoadHolds rd (P.rb * gen ^ i) 0 (P.acc * (gen ^ i) ^ 129) ∧
      LoadHolds rd (P.acc * (gen ^ i) ^ 129 * gen ^ j) 0 (accSum syms ws i j) ∧
      LoadHolds rd (P.acc * (gen ^ i) ^ 129 * gen ^ j) 1
        (accSum syms ws i j + cellDot syms ws i j) ∧
      LoadHolds rd (P.node j * (gen ^ i * gen ^ i)) 0 (digestScalars (cellD syms i j)).1 ∧
      LoadHolds rd (P.node j * (gen ^ i * gen ^ i)) 1 (digestScalars (cellD syms i j)).2 := by
    intro i hi
    have hi2 : i < 2 ^ L := by omega
    obtain ⟨n0, n1⟩ := treeMem_leaf (hm.node j hj) (length_nodeLeaves r L syms j) hi2
    rw [nodeLeaves_getD r L syms j hi2, cellLeaf, ite_pos' hi] at n0 n1
    refine ⟨hcellR i hi, hm.rbase i hi, ?_, ?_, by rw [gen_sq]; exact n0, by rw [gen_sq]; exact n1⟩
    · rcases hacc i hi j (by omega) with h | h
      · simpa using h
      · omega
    · rcases hacc i hi (j + 1) (by omega) with h | h
      · rw [show j + 1 - j = 1 by omega, accSum, Finset.sum_range_succ] at h
        exact h
      · omega
  have hpre : ∀ i < r, j < 64 → LoadHolds rd (P.pb * gen ^ i) 0 (P.pd * (gen ^ i) ^ 128) ∧
      LoadHolds rd (P.pd * (gen ^ i) ^ 128 * (gen ^ j * gen ^ j)) 0 (digestScalars (cellD syms i j)).1 ∧
      LoadHolds rd (P.pd * (gen ^ i) ^ 128 * (gen ^ j * gen ^ j)) 1 (digestScalars (cellD syms i j)).2 := by
    intro i hi h64
    have q0 := reads_pair (hm.pcells i hi) (f := fun j => digestCells (cellD syms i j))
      (fun _ => rfl) h64 (k := 0) (by omega)
    have q1 := reads_pair (hm.pcells i hi) (f := fun j => digestCells (cellD syms i j))
      (fun _ => rfl) h64 (k := 1) (by omega)
    rw [← gen_sq] at q0 q1
    exact ⟨hm.pbase i hi, q0, q1⟩
  -- the padding rows
  have hgap : ∀ d < 2 ^ L - r,
      LoadHolds rd (P.node j * (gen ^ r * gen ^ r) * (gen ^ d * gen ^ d)) 0
        (digestScalars daPadCellDigest).1 ∧
      LoadHolds rd (P.node j * (gen ^ r * gen ^ r) * (gen ^ d * gen ^ d)) 1
        (digestScalars daPadCellDigest).2 := by
    intro d hd
    have hrd : r + d < 2 ^ L := by omega
    obtain ⟨n0, n1⟩ := treeMem_leaf (hm.node j hj) (length_nodeLeaves r L syms j) hrd
    rw [nodeLeaves_getD r L syms j hrd, cellLeaf, ite_neg' (by omega)] at n0 n1
    have e : P.node j * (gen ^ r * gen ^ r) * (gen ^ d * gen ^ d) = P.node j * gen ^ (2 * (r + d)) := by
      rw [gen_sq, gen_sq, mul_assoc, ← pow_add]; congr 2; ring
    rw [e]
    exact ⟨n0, n1⟩
  -- the tree and its root
  have hlev := da_levels_complete L hL rd (P.node j) (nodeLeaves r L syms j)
    (length_nodeLeaves r L syms j) (fun _ => canon_nodeLeaves r L syms j) (hm.node j hj)
  have hroot : cellRoot L (nodeLeaves r L syms j) = digestScalars (mRoot L (cellLeaf r syms j)) := by
    rw [nodeLeaves]; exact cellRoot_mRoot L _
  have hct := treeMem_leaf hm.ct (by simp [colLeaves]) (i := j) (by norm_num; omega)
  have hcj : (colLeaves r L syms).getD j 0 = digestScalars (mRoot L (cellLeaf r syms j)) := by
    simp [colLeaves, List.getD_eq_getElem?_getD, hj]
  rw [hcj, ← hroot, ← gen_sq] at hct
  by_cases h64 : j < 64
  · rw [ite_pos' h64]
    have hc := col1_ok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hcp : (coreProgram.getD 769 default).params = (List.range 9).map V.n := by
      have := hc.1
      unfold colOk at this
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    have hidx417 : coreProgram.indexOf? "__loop417" = some 895 := by
      have h := row417_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
    have hidx418 : coreProgram.indexOf? "__loop418" = some 896 := by
      have h := gap418_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
    refine col_rel (find_of_idx hc.2 (by rw [coreProgram_length]; omega)) core769_body hcp
      (find_of_idx hidx417 (by rw [coreProgram_length]; omega)) row417_shape.1
      (find_of_idx hidx418 (by rw [coreProgram_length]; omega)) gap418_shape.1 hL hvec
      (fun i hi => ?_) (fun d hd => ?_) hlev hct.1 hct.2
    · obtain ⟨hc', ha, hp, hn, h0, h1⟩ := hrow i hi
      obtain ⟨hpp, hq0, hq1⟩ := hpre i hi h64
      exact row_block1 hc' ha hp hn h0 h1 hpp hq0 hq1
    · obtain ⟨g0, g1⟩ := hgap d hd
      exact gap_block gap418_shape.1 gap418_shape.2 core896_body g0 g1
  · rw [ite_neg' h64]
    have hc := col0_ok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hcp : (coreProgram.getD 770 default).params = (List.range 9).map V.n := by
      have := hc.1
      unfold colOk at this
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    have hidx419 : coreProgram.indexOf? "__loop419" = some 897 := by
      have h := row419_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
    have hidx420 : coreProgram.indexOf? "__loop420" = some 898 := by
      have h := gap420_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
    refine col_rel (find_of_idx hc.2 (by rw [coreProgram_length]; omega)) core770_body hcp
      (find_of_idx hidx419 (by rw [coreProgram_length]; omega)) row419_shape.1
      (find_of_idx hidx420 (by rw [coreProgram_length]; omega)) gap420_shape.1 hL hvec
      (fun i hi => ?_) (fun d hd => ?_) hlev hct.1 hct.2
    · obtain ⟨hc', ha, hp, hn, h0, h1⟩ := hrow i hi
      exact row_block0 (pb := P.pb) hc' ha hp hn h0 h1
    · obtain ⟨g0, g1⟩ := hgap d hd
      exact gap_block gap420_shape.1 gap420_shape.2 core898_body g0 g1

end
end LeanVM.Guest.B1.Da
