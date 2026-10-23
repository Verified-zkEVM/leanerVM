/-
  LeanVM.Guest.B1.Eq.EqTreeFrame

  The expansion of the guest's inline `eqtree_frame`: the equality kernel of a point in frame
  cells, the last level cut at a count.
-/

module

public import LeanVM.Guest.B1.Eq.EqTree

/-!
# `eqtree_frame` (G:844-857, TRIAGE #24)

`eqtree_frame(point_ptr, out, n, count)` is `eqtree` into frame cells, the last level's upper
half cut at `count`. Its cells are values, numbered in the order the expansion computes them:
from the value `b` (the point read at `p` from `po`; `keccak_layer`, `keccak_slot_lanes`,
G:2692-2764, number it), `r0` at `b`, level 1's cells `1 + r0`, `r0` at `b + 2`, `b + 3`; level
`k + 1` (`k ≥ 1`) from the block `eqtreeFrameL b k`: `r_k`, `1 + r_k`, then for each cell `i` of
level `k` in order its products by `1 + r_k` (cell `i`) and by `r_k` (cell `2^k + i`, the latter
omitted past `count` at the last level).

* `efCell b n count m j`: the value of cell `j` of level `m`;
* `eqtreeFrame_sound`: with the point's words `rs` at `p` from `po`, cell `j` of level `m ≤ n` is
  `eqKernel (rs.take m)` entry `j` (`eqKernel`, V:642), the last level's cells below `count`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The first value of block `k ≥ 1` (blocks before the last are uncut). -/
def eqtreeFrameL (b k : ℕ) : ℕ := b + 3 * k + 2 ^ (k + 1) - 3

/-- How many upper cells block `k` writes: all `2^k`, or `count - 2^k` at the last block. -/
def efC (n count k : ℕ) : ℕ := if k + 1 = n then count - 2 ^ k else 2 ^ k

/-- The value of cell `j` of level `m ≥ 1`. -/
def efCell (b n count m j : ℕ) : ℕ :=
  if m ≤ 1 then b + 2 + j
  else if j < 2 ^ (m - 1) then eqtreeFrameL b (m - 1) + 3 + j + min j (efC n count (m - 1))
  else eqtreeFrameL b (m - 1) + 4 + 2 * (j - 2 ^ (m - 1))

/-- Cell `i` of level `k`'s products in block `k`. -/
def efWordT (b n count k i : ℕ) : List Stmt :=
  let L := eqtreeFrameL b k
  let lo := L + 3 + i + min i (efC n count k)
  if i < efC n count k then
    [.atom (.mul (.n lo) (.n (efCell b n count k i)) (.n (L + 2))),
      .atom (.mul (.n (lo + 1)) (.n (efCell b n count k i)) (.n L))]
  else [.atom (.mul (.n lo) (.n (efCell b n count k i)) (.n (L + 2)))]

/-- Block `k ≥ 1`. -/
def efBlockT (p : V) (po b n count k : ℕ) : List Stmt :=
  let L := eqtreeFrameL b k
  [.atom (.load (.n L) p (po + k)), .atom (.const (.n (L + 1)) (word 1 0 0)),
    .atom (.add (.n (L + 2)) (.n (L + 1)) (.n L))] ++
    ((List.range (2 ^ k)).map (efWordT b n count k)).flatten

/-- **`eqtree_frame(point, out, n, count)`** from the value `b`. -/
def eqtreeFrameT (p : V) (po b n count : ℕ) : List Stmt :=
  [.atom (.load (.n b) p po), .atom (.const (.n (b + 1)) (word 1 0 0)),
    .atom (.add (.n (b + 2)) (.n (b + 1)) (.n b)), .atom (.copy (.n (b + 3)) (.n b))] ++
    ((List.range (n - 1)).map fun k ↦ efBlockT p po b n count (k + 1)).flatten

theorem eqtreeFrameT_atoms (p : V) (po b n count : ℕ) : AllAtoms (eqtreeFrameT p po b n count) := by
  unfold eqtreeFrameT
  refine allAtoms_append ?_ (allAtoms_map_flatten fun k _ => ?_)
  · exact allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil)))
  · unfold efBlockT
    refine allAtoms_append (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil)))
      (allAtoms_map_flatten fun i _ => ?_)
    unfold efWordT
    dsimp only
    split
    · exact allAtoms_cons (allAtoms_cons allAtoms_nil)
    · exact allAtoms_cons allAtoms_nil

/-- **`eqtree_frame`** (G:844-857): with the point's words `rs` (`n ≥ 1` of them) at `p` from
`po`, cell `j` of level `m ≤ n` is entry `j` of `eqKernel (rs.take m)`, below `count` at the last
level. -/
theorem eqtreeFrame_sound {p : V} {po b n count : ℕ} (hn : 1 ≤ n)
    (hA : ∀ a, Stmt.atom a ∈ eqtreeFrameT p po b n count → a.Holds rd σ) {rs : List E}
    (hrs : rs.length = n) (hpt : ∀ t < n, LoadHolds rd (σ p) (po + t) (rs.getD t 0)) :
    ∀ m, 1 ≤ m → m ≤ n → ∀ j < 2 ^ m, (m < n ∨ j < count) →
      σ (.n (efCell b n count m j)) = (eqKernel (rs.take m)).getD j 0 := by
  intro m hm1 hmn
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have a0 := hA _ (by simp [eqtreeFrameT] : Stmt.atom (.load (.n b) p po) ∈ _)
      have a1 := hA _ (by simp [eqtreeFrameT] : Stmt.atom (.const (.n (b + 1)) (word 1 0 0)) ∈ _)
      have a2 := hA _ (by simp [eqtreeFrameT] : Stmt.atom (.add (.n (b + 2)) (.n (b + 1)) (.n b)) ∈ _)
      have a3 := hA _ (by simp [eqtreeFrameT] : Stmt.atom (.copy (.n (b + 3)) (.n b)) ∈ _)
      simp only [Atom.Holds] at a1 a2 a3
      rcases rs with _ | ⟨r0, rest⟩
      · simp at hrs; omega
      have hr0 : σ (.n b) = r0 := loadHolds_unique a0 (by simpa using hpt 0 hn)
      have hk : eqKernel ((r0 :: rest).take (0 + 1)) = [1 + r0, r0] := by simp [eqKernel]
      intro j hj _
      rw [hk]
      simp only [efCell, le_refl, ↓reduceIte]
      interval_cases j
      · rw [a2, a1, word_one, hr0]; rfl
      · rw [a3, hr0]; rfl
    · have memB : ∀ a, Stmt.atom a ∈ efBlockT p po b n count m → a.Holds rd σ := fun a ha =>
        hA a (by
          unfold eqtreeFrameT
          refine List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
            ⟨m - 1, List.mem_range.mpr (by omega), ?_⟩, ha⟩)
          rw [Nat.sub_add_cancel (by omega)])
      set L := eqtreeFrameL b m with hL
      have l0 := memB _ (by simp [efBlockT, ← hL] : Stmt.atom (.load (.n L) p (po + m)) ∈ _)
      have l1 := memB _ (by simp [efBlockT, ← hL] : Stmt.atom (.const (.n (L + 1)) (word 1 0 0)) ∈ _)
      have l2 := memB _ (by simp [efBlockT, ← hL] :
        Stmt.atom (.add (.n (L + 2)) (.n (L + 1)) (.n L)) ∈ _)
      simp only [Atom.Holds] at l1 l2
      have hrt : σ (.n L) = rs.getD m 0 := loadHolds_unique l0 (hpt m (by omega))
      have hrt1 : σ (.n (L + 2)) = 1 + rs.getD m 0 := by rw [l2, l1, word_one, hrt]
      have word := fun i (hi : i < 2 ^ m) (a : Atom) (ha : Stmt.atom a ∈ efWordT b n count m i) =>
        memB a (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
          ⟨i, List.mem_range.mpr hi, rfl⟩, ha⟩))
      have htake : rs.take (m + 1) = rs.take m ++ [rs.getD m 0] := by
        rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        simp
      have hlen : (eqKernel (rs.take m)).length = 2 ^ m := by
        rw [length_eqKernel_eq]; simp [hrs]; omega
      intro j hj hjc
      rw [htake, eqKernel_snoc]
      by_cases hlo : j < 2 ^ m
      · have w := word j hlo _ (by
          unfold efWordT; dsimp only; split <;> simp [← hL] :
          Stmt.atom (.mul (.n (L + 3 + j + min j (efC n count m))) (.n (efCell b n count m j))
            (.n (L + 2))) ∈ _)
        simp only [Atom.Holds] at w
        have ih' := ih (by omega) (by omega) j hlo (Or.inl (by omega))
        rw [List.getD_append _ _ _ _ (by rw [List.length_map, hlen]; exact hlo), getD_map_mul_eq,
          ← ih', ← hrt1, ← w]
        simp only [efCell, show ¬ m + 1 ≤ 1 by omega, ↓reduceIte, hlo, Nat.add_sub_cancel, ← hL]
      · obtain ⟨i, hi, rfl⟩ : ∃ i < 2 ^ m, j = 2 ^ m + i :=
          ⟨j - 2 ^ m, by rw [pow_succ] at hj; omega, by omega⟩
        have hic : i < efC n count m := by
          unfold efC
          split
          · rcases hjc with h | h <;> omega
          · exact hi
        have w := word i hi _ (by
          unfold efWordT; dsimp only; simp [hic, ← hL] :
          Stmt.atom (.mul (.n (L + 3 + i + min i (efC n count m) + 1)) (.n (efCell b n count m i))
            (.n L)) ∈ _)
        simp only [Atom.Holds] at w
        have ih' := ih (by omega) (by omega) i hi (Or.inl (by omega))
        rw [List.getD_append_right _ _ _ _ (by rw [List.length_map, hlen]; omega), List.length_map,
          hlen, Nat.add_sub_cancel_left, getD_map_mul_eq, ← ih', ← hrt, ← w]
        simp only [efCell, show ¬ m + 1 ≤ 1 by omega, ↓reduceIte, Nat.add_sub_cancel, ← hL,
          show ¬ 2 ^ m + i < 2 ^ m by omega, Nat.add_sub_cancel_left, min_eq_left (le_of_lt hic)]
        congr 2; omega

/-! ## The honest values -/

/-- The length of block `k ≥ 1`. -/
def efLen (n count k : ℕ) : ℕ := 3 + 2 ^ k + efC n count k

/-- The honest value at offset `o` of block `k ≥ 1`: `r_k`, `1`, `1 + r_k`, then for each cell `i`
of level `k` in order `e_i·(1 + r_k)` and, below `efC`, `e_i·r_k`. -/
def efLvlVal (rs : List E) (n count k o : ℕ) : E :=
  let r := rs.getD k 0
  let c := efC n count k
  if o = 0 then r else if o = 1 then 1 else if o = 2 then 1 + r
  else if o - 3 < 2 * c then
    let e := (eqKernel (rs.take k)).getD ((o - 3) / 2) 0
    if (o - 3) % 2 = 0 then e * (1 + r) else e * r
  else (eqKernel (rs.take k)).getD (c + (o - 3 - 2 * c)) 0 * (1 + r)

theorem efLvlVal_lo (rs : List E) (n count k i : ℕ) :
    efLvlVal rs n count k (3 + i + min i (efC n count k)) =
      (eqKernel (rs.take k)).getD i 0 * (1 + rs.getD k 0) := by
  simp only [efLvlVal, show ¬ 3 + i + min i (efC n count k) = 0 by omega,
    show ¬ 3 + i + min i (efC n count k) = 1 by omega,
    show ¬ 3 + i + min i (efC n count k) = 2 by omega, ↓reduceIte]
  rcases Nat.lt_or_ge i (efC n count k) with h | h
  · rw [min_eq_left (le_of_lt h)]
    simp only [show 3 + i + i - 3 < 2 * efC n count k by omega, ↓reduceIte,
      show (3 + i + i - 3) / 2 = i by omega, show (3 + i + i - 3) % 2 = 0 by omega]
  · rw [min_eq_right h]
    simp only [show ¬ 3 + i + efC n count k - 3 < 2 * efC n count k by omega, ↓reduceIte]
    congr 2; omega

theorem efLvlVal_hi (rs : List E) (n count k i : ℕ) (hi : i < efC n count k) :
    efLvlVal rs n count k (3 + i + min i (efC n count k) + 1) =
      (eqKernel (rs.take k)).getD i 0 * rs.getD k 0 := by
  rw [min_eq_left (le_of_lt hi)]
  simp only [efLvlVal, show ¬ 3 + i + i + 1 = 0 by omega, show ¬ 3 + i + i + 1 = 1 by omega,
    show ¬ 3 + i + i + 1 = 2 by omega, ↓reduceIte, show 3 + i + i + 1 - 3 < 2 * efC n count k by omega,
    show (3 + i + i + 1 - 3) / 2 = i by omega, show (3 + i + i + 1 - 3) % 2 = 1 by omega]
  rfl

/-- The cells hold the equality kernel, from the honest values. -/
theorem efCell_of_vals {b n count : ℕ} {rs : List E}
    (hhead : ∀ k < 4, σ (.n (b + k)) = [rs.getD 0 0, 1, 1 + rs.getD 0 0, rs.getD 0 0].getD k 0)
    (hlvl : ∀ k, 1 ≤ k → k < n → ∀ o < efLen n count k,
      σ (.n (eqtreeFrameL b k + o)) = efLvlVal rs n count k o) (hrs : rs.length = n) :
    ∀ m, 1 ≤ m → m ≤ n → ∀ j < 2 ^ m, (j < 2 ^ (m - 1) ∨ j - 2 ^ (m - 1) < efC n count (m - 1) ∨ m = 1) →
      σ (.n (efCell b n count m j)) = (eqKernel (rs.take m)).getD j 0 := by
  intro m hm1 hmn j hj hc
  rcases Nat.eq_or_lt_of_le hm1 with rfl | hm
  · rcases rs with _ | ⟨r0, rest⟩
    · simp at hrs; omega
    have hk : eqKernel ((r0 :: rest).take 1) = [1 + r0, r0] := by simp [eqKernel]
    rw [hk]
    simp only [efCell, le_refl, ↓reduceIte]
    interval_cases j
    · simpa using hhead 2 (by omega)
    · simpa using hhead 3 (by omega)
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have htake : rs.take (k + 1) = rs.take k ++ [rs.getD k 0] := by
      rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      simp
    have hlen : (eqKernel (rs.take k)).length = 2 ^ k := by
      rw [length_eqKernel_eq]; simp [hrs]; omega
    rw [htake, eqKernel_snoc]
    simp only [efCell, show ¬ k + 1 ≤ 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
    by_cases hlo : j < 2 ^ k
    · simp only [hlo, ↓reduceIte]
      rw [show eqtreeFrameL b k + 3 + j + min j (efC n count k) =
        eqtreeFrameL b k + (3 + j + min j (efC n count k)) by ring,
        hlvl k hk1 (by omega) _ (by unfold efLen; have := min_le_right j (efC n count k); omega),
        efLvlVal_lo, List.getD_append _ _ _ _ (by rw [List.length_map, hlen]; exact hlo),
        getD_map_mul_eq]
    · simp only [hlo, ↓reduceIte]
      obtain ⟨i, rfl⟩ : ∃ i, j = 2 ^ k + i := ⟨j - 2 ^ k, by omega⟩
      have hi : i < efC n count k := by simp at hc; omega
      rw [show 2 ^ k + i - 2 ^ k = i by omega,
        show eqtreeFrameL b k + 4 + 2 * i = eqtreeFrameL b k + (3 + i + min i (efC n count k) + 1) by
          rw [min_eq_left (le_of_lt hi)]; ring,
        hlvl k hk1 (by omega) _ (by unfold efLen; omega), efLvlVal_hi _ _ _ _ _ hi,
        List.getD_append_right _ _ _ _ (by rw [List.length_map, hlen]; omega), List.length_map, hlen,
        Nat.add_sub_cancel_left, getD_map_mul_eq]

/-- **The honest values satisfy `eqtree_frame`**: with the point's words at `p` and the template's
values `r_0, 1, 1 + r_0, r_0` and each block's `efLvlVal`. -/
theorem eqtreeFrameT_complete {p : V} {po b n count : ℕ} {rs : List E} (hrs : rs.length = n)
    (hn : 1 ≤ n) (hpt : ∀ t < n, LoadHolds rd (σ p) (po + t) (rs.getD t 0))
    (hhead : ∀ k < 4, σ (.n (b + k)) = [rs.getD 0 0, 1, 1 + rs.getD 0 0, rs.getD 0 0].getD k 0)
    (hlvl : ∀ k, 1 ≤ k → k < n → ∀ o < efLen n count k,
      σ (.n (eqtreeFrameL b k + o)) = efLvlVal rs n count k o) :
    ∀ a, Stmt.atom a ∈ eqtreeFrameT p po b n count → a.Holds rd σ := by
  intro a ha
  have h0 : σ (.n b) = rs.getD 0 0 := hhead 0 (by omega)
  have h1 : σ (.n (b + 1)) = 1 := hhead 1 (by omega)
  have h2 : σ (.n (b + 2)) = 1 + rs.getD 0 0 := hhead 2 (by omega)
  have h3 : σ (.n (b + 3)) = rs.getD 0 0 := hhead 3 (by omega)
  simp only [eqtreeFrameT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatten, List.mem_map, List.mem_range] at ha
  rcases ha with (h | h | h | h) | ⟨blk, ⟨k', hk', rfl⟩, hb⟩
  all_goals try (obtain rfl := Stmt.atom.inj h)
  · show LoadHolds rd (σ p) po (σ (.n b)); rw [h0]; simpa using hpt 0 (by omega)
  · show σ (.n (b + 1)) = word 1 0 0; rw [h1, word_one]
  · show σ (.n (b + 2)) = σ (.n (b + 1)) + σ (.n b); rw [h2, h1, h0]
  · show σ (.n (b + 3)) = σ (.n b); rw [h3, h0]
  · set k := k' + 1 with hk
    have hkn : k < n := by omega
    set L := eqtreeFrameL b k with hL
    have v := hlvl k (by omega) hkn
    have hlen3 : 3 ≤ efLen n count k :=
      le_trans (Nat.le_add_right 3 (2 ^ k)) (Nat.le_add_right _ _)
    have vr : σ (.n L) = rs.getD k 0 := by simpa [efLvlVal] using v 0 (by omega)
    have v1 : σ (.n (L + 1)) = 1 := by simpa [efLvlVal] using v 1 (by omega)
    have v2 : σ (.n (L + 2)) = 1 + rs.getD k 0 := by simpa [efLvlVal] using v 2 (by omega)
    simp only [efBlockT, ← hL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatten, List.mem_map, List.mem_range] at hb
    rcases hb with (h | h | h) | ⟨w, ⟨i, hi, rfl⟩, hw⟩
    all_goals try (obtain rfl := Stmt.atom.inj h)
    · show LoadHolds rd (σ p) (po + k) (σ (.n L)); rw [vr]; exact hpt k hkn
    · show σ (.n (L + 1)) = word 1 0 0; rw [v1, word_one]
    · show σ (.n (L + 2)) = σ (.n (L + 1)) + σ (.n L); rw [v2, v1, vr]
    · have hcell : σ (.n (efCell b n count k i)) = (eqKernel (rs.take k)).getD i 0 := by
        refine efCell_of_vals hhead hlvl hrs k (by omega) (by omega) i hi ?_
        rcases Nat.eq_or_lt_of_le (show 1 ≤ k by omega) with h | h
        · exact Or.inr (Or.inr h.symm)
        · right; left
          have : efC n count (k - 1) = 2 ^ (k - 1) := by
            unfold efC; simp only [show ¬ (k - 1 + 1 = n) by omega, ↓reduceIte]
          rw [this]
          have : 2 ^ k = 2 * 2 ^ (k - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel (by omega)]
          omega
      have vlo : σ (.n (L + 3 + i + min i (efC n count k))) =
          (eqKernel (rs.take k)).getD i 0 * (1 + rs.getD k 0) := by
        rw [show L + 3 + i + min i (efC n count k) = L + (3 + i + min i (efC n count k)) by ring,
          v _ (by unfold efLen; have := min_le_right i (efC n count k); omega), efLvlVal_lo]
      simp only [efWordT, ← hL] at hw
      split at hw
      · rename_i hic
        have vhi : σ (.n (L + 3 + i + min i (efC n count k) + 1)) =
            (eqKernel (rs.take k)).getD i 0 * rs.getD k 0 := by
          rw [show L + 3 + i + min i (efC n count k) + 1 = L + (3 + i + min i (efC n count k) + 1) by ring,
            v _ (by unfold efLen; rw [min_eq_left (le_of_lt hic)]; omega), efLvlVal_hi _ _ _ _ _ hic]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with h | h <;> obtain rfl := Stmt.atom.inj h
        · show σ (.n (L + 3 + i + min i (efC n count k))) = σ (.n (efCell b n count k i)) * σ (.n (L + 2))
          rw [vlo, hcell, v2]
        · show σ (.n (L + 3 + i + min i (efC n count k) + 1)) = σ (.n (efCell b n count k i)) * σ (.n L)
          rw [vhi, hcell, vr]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        obtain rfl := Stmt.atom.inj hw
        show σ (.n (L + 3 + i + min i (efC n count k))) = σ (.n (efCell b n count k i)) * σ (.n (L + 2))
        rw [vlo, hcell, v2]

end
end LeanVM.Guest.B1
