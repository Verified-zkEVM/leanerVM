/-
  LeanVM.Guest.B1.Terminal.Layout

  The layout facts `check_opening_terminal` needs: where `placementsOf` puts a committed column
  and a column with a `q_keccak` slot, and that every offset and size fits the stack.
-/

module

public import LeanVM.Guest.B1.Terminal.Interface
public import LeanVM.Guest.B1.Placement.Kappas

/-!
# The layout

`placementsOf kappas` (V:997-1012) places the committed columns (`committedCols`, all but the
`KECCAK` columns with a `q_keccak` slot and its output lanes) at `stackOffsets`'s offsets and each
slotted column at `q_keccak`'s offset plus its slot's `2^κ` words (`placement_committed`,
`placement_slot`). Every offset is below
`2^stackLog` (`stackOffsets_lt`) and every size at most `stackLog` (`size_le_stackLog`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `KECCAK`'s output lanes are global columns `111 .. 135`. -/
theorem keccakOutputColumns_eq : keccakOutputColumns = (List.range 25).map (111 + ·) := by
  decide +kernel

/-- The `q_keccak` slots of the global columns (`KECCAK_SLOT_OF`, V:951-953): the input lanes
`86 .. 110` at slots `0 .. 24`, `KECCAK`'s first thirteen committed columns `73 .. 85` at slots
`50 .. 62`, its first read count `136` at slot `63`. -/
def slotOfCol (c : ℕ) : Option ℕ :=
  if 86 ≤ c ∧ c < 111 then some (c - 86) else if 73 ≤ c ∧ c < 86 then some (c - 23)
  else if c = 136 then some 63 else none

theorem keccakSlot_eq_all :
    (List.range 163).all (fun c ↦ keccakSlot c == slotOfCol c) = true := by
  decide +kernel

theorem keccakSlot_eq {c : ℕ} (hc : c < 163) : keccakSlot c = slotOfCol c := by
  have := List.all_eq_true.mp keccakSlot_eq_all c (List.mem_range.mpr hc)
  simpa using this

/-- Committed column `cc`'s global column: `0 .. 72`, then `137 .. 162`. -/
def colOfCommitted (cc : ℕ) : ℕ := if cc < 73 then cc else cc + 64

theorem committedCols_idxOf_all :
    (List.range Tables.nCommittedCols).all
      (fun cc ↦ (Tables.committedCols 163).idxOf ((Tables.committedCols 163).getD cc 0) == cc) =
      true := by
  rw [Tables.committedCols_163]; decide +kernel

theorem committedCols_idxOf {cc : ℕ} (hcc : cc < Tables.nCommittedCols) :
    (Tables.committedCols 163).idxOf ((Tables.committedCols 163).getD cc 0) = cc := by
  have := List.all_eq_true.mp committedCols_idxOf_all cc (List.mem_range.mpr hcc)
  simpa using this

/-- Committed column `cc`'s global column. -/
theorem committedCols_getD {cc : ℕ} (hcc : cc < Tables.nCommittedCols) :
    (Tables.committedCols 163).getD cc 0 = colOfCommitted cc := by
  have hcc' : cc < 99 := hcc
  rw [Tables.committedCols_163, List.getD_eq_getElem _ _ (by simp; omega), colOfCommitted]
  split
  · rw [List.getElem_append_left (by simpa using ‹cc < 73›)]; simp
  · rw [List.getElem_append_right (by simp; omega)]; simp; omega

theorem colOfCommitted_all :
    (List.range Tables.nCommittedCols).all (fun cc ↦ decide (colOfCommitted cc < 163) &&
      slotOfCol (colOfCommitted cc) == none &&
      decide (colOfCommitted cc ∉ keccakOutputColumns)) = true := by
  rw [keccakOutputColumns_eq]; decide +kernel

theorem colOfCommitted_facts {cc : ℕ} (hcc : cc < Tables.nCommittedCols) :
    colOfCommitted cc < 163 ∧ slotOfCol (colOfCommitted cc) = none ∧
      colOfCommitted cc ∉ keccakOutputColumns := by
  have := List.all_eq_true.mp colOfCommitted_all cc (List.mem_range.mpr hcc)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- The placements, column by column. -/
theorem placementsOf_getD (kappas : List ℕ) {g : ℕ} (hg : g < kappas.length) :
    (placementsOf kappas).1.getD g none =
      match keccakSlot g with
      | some slot => some (Placement.mk (kappas.getD g 0)
          ((stackOffsets (Tables.committedKappas kappas)).1.getD
            ((Tables.committedCols kappas.length).idxOf qkeccak) 0 + slot * 2 ^ kappas.getD g 0) 0)
      | none =>
        if g ∈ keccakOutputColumns then none else some (Placement.mk (kappas.getD g 0)
          ((stackOffsets (Tables.committedKappas kappas)).1.getD
            ((Tables.committedCols kappas.length).idxOf g) 0) 0) := by
  unfold placementsOf Tables.committedKappas Tables.committedCols
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
    List.getElem?_eq_getElem hg, Option.map_some, Option.getD_some, zero_add]
  rfl

theorem placementsOf_snd (kappas : List ℕ) :
    (placementsOf kappas).2 = max minStackedLog (stackOffsets (Tables.committedKappas kappas)).2 :=
  rfl

/-- **A committed column's placement**: its size and `stackOffsets`'s offset. -/
theorem placement_committed {layout : Layout} {kappas : List ℕ} (hl : kappas.length = 163)
    (hP : layout.placements = (placementsOf kappas).1) {cc : ℕ} (hcc : cc < Tables.nCommittedCols) :
    layout.placement ((Tables.committedCols 163).getD cc 0) =
      Placement.mk ((Tables.committedKappas kappas).getD cc 0)
        ((stackOffsets (Tables.committedKappas kappas)).1.getD cc 0) 0 := by
  have hg := committedCols_getD hcc
  obtain ⟨hglt, hs, ho⟩ := colOfCommitted_facts hcc
  rw [← hg] at hglt hs ho
  rw [Layout.placement, hP, placementsOf_getD _ (by rw [hl]; exact hglt), keccakSlot_eq hglt, hs, hl,
    committedCols_idxOf hcc]
  simp only [ho, ↓reduceIte, Option.getD_some]
  have hlen : cc < (Tables.committedCols 163).length := by
    rw [Tables.committedCols_163_length]; exact hcc
  have e : (Tables.committedKappas kappas).getD cc 0 =
      kappas.getD ((Tables.committedCols 163).getD cc 0) 0 := by
    rw [Tables.committedKappas, hl, List.getD_eq_getElem _ _ (by simpa using hlen),
      List.getElem_map, List.getD_eq_getElem _ _ hlen]
  rw [e]

/-- **A slotted column's placement** (an input lane or a spare slot's column): its size,
`q_keccak`'s offset plus its slot's `2^κ` words. -/
theorem placement_slot {layout : Layout} {kappas : List ℕ} (hl : kappas.length = 163)
    (hP : layout.placements = (placementsOf kappas).1) {g s : ℕ} (hg : g < 163)
    (hs : slotOfCol g = some s) :
    layout.placement g =
      Placement.mk (kappas.getD g 0) ((stackOffsets (Tables.committedKappas kappas)).1.getD 5 0 +
          s * 2 ^ kappas.getD g 0) 0 := by
  have h5 := committedCols_idxOf (cc := 5) (by decide)
  rw [committedCols_getD (by decide)] at h5
  rw [Layout.placement, hP, placementsOf_getD _ (by omega), keccakSlot_eq hg, hs, hl]
  rw [show qkeccak = 5 from rfl, show colOfCommitted 5 = 5 from rfl] at *
  rw [h5]
  rfl

/-! ## Offsets and sizes -/

theorem le_two_pow_log2Ceil (N : ℕ) : N ≤ 2 ^ log2Ceil N := log2Ceil_le_iff.mp le_rfl

/-- The fold of `stackOffsets` keeps every entry `0` or below the running total. -/
theorem stackOffsets_fold (size : ℕ → ℕ) : ∀ (order : List ℕ) (acc : List ℕ × ℕ),
    (∀ i, acc.1.getD i 0 = 0 ∨ acc.1.getD i 0 < acc.2) →
    let r := order.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ size i)) acc
    (∀ i, r.1.getD i 0 = 0 ∨ r.1.getD i 0 < r.2) ∧ r.2 = acc.2 + (order.map (2 ^ size ·)).sum
  | [], acc, h => by simpa using h
  | k :: order, acc, h => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have step : ∀ i, (acc.1.set k acc.2).getD i 0 = 0 ∨
        (acc.1.set k acc.2).getD i 0 < acc.2 + 2 ^ size k := by
      intro i
      rw [List.getD_eq_getElem?_getD, List.getElem?_set]
      split
      · split
        · right; simp only [Option.getD_some]; have := Nat.one_le_two_pow (n := size k); omega
        · left; rfl
      · rw [← List.getD_eq_getElem?_getD]
        rcases h i with h0 | hlt
        · left; exact h0
        · right; exact lt_of_lt_of_le hlt (Nat.le_add_right _ _)
    obtain ⟨h1, h2⟩ := stackOffsets_fold size order (acc.1.set k acc.2, acc.2 + 2 ^ size k) step
    exact ⟨h1, by rw [h2]; ring⟩

/-- **Every offset is below `2^totalLog`.** -/
theorem stackOffsets_lt (sizes : List ℕ) (i : ℕ) :
    (stackOffsets sizes).1.getD i 0 < 2 ^ (stackOffsets sizes).2 := by
  unfold stackOffsets
  obtain ⟨h1, h2⟩ := stackOffsets_fold (fun i ↦ sizes.getD i 0)
    ((List.range sizes.length).mergeSort fun i j ↦ decide (sizes.getD j 0 < sizes.getD i 0) ||
      (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j)))
    (List.replicate sizes.length 0, 0) (fun i ↦ by
      left; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl)
  simp only at h1 h2 ⊢
  rcases h1 i with h0 | hlt
  · rw [h0]; exact Nat.two_pow_pos _
  · exact lt_of_lt_of_le hlt (le_two_pow_log2Ceil _)

/-- The total `stackOffsets` lays out is the sum of the blocks. -/
theorem stackOffsets_total (sizes : List ℕ) :
    2 ^ (stackOffsets sizes).2 ≥ (sizes.map (2 ^ ·)).sum := by
  unfold stackOffsets
  obtain ⟨-, h2⟩ := stackOffsets_fold (fun i ↦ sizes.getD i 0)
    ((List.range sizes.length).mergeSort fun i j ↦ decide (sizes.getD j 0 < sizes.getD i 0) ||
      (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j)))
    (List.replicate sizes.length 0, 0) (fun i ↦ by
      left; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl)
  simp only at h2 ⊢
  refine le_trans (le_of_eq ?_) (le_two_pow_log2Ceil _)
  rw [h2, zero_add, ((List.mergeSort_perm _ _).map _).sum_eq]
  have : (List.range sizes.length).map (fun i ↦ 2 ^ sizes.getD i 0) = sizes.map (2 ^ ·) := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using h2)]
    rfl
  rw [this]

/-- **Every size is at most the total's log.** -/
theorem size_le_stackOffsets (sizes : List ℕ) {i : ℕ} (hi : i < sizes.length) :
    sizes.getD i 0 ≤ (stackOffsets sizes).2 := by
  have h1 := Tables.tb_single_le_sum_map sizes i hi
  have h2 := stackOffsets_total sizes
  by_contra hc
  have : 2 ^ (stackOffsets sizes).2 < 2 ^ sizes.getD i 0 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  omega

end
end LeanVM.Guest.B1.VerifySub
