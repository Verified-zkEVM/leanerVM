module

public import LeanVM.Cost.Decoder.EntryTable
public import LeanVM.Cost.Decoder.GuestTablesCheck

/-!
# The replayed frame map, restated, is the deployed one

At the guest's tables (`GuestTablesCheck.lean`): `pcTableT = pcTable`, `entryTableT pcTable =
entryTable`, and **`frameAt_eq`**: the closure `frameAt (entryTableT pcTableT pre states rd) rd`
is `Guest.Fast.frameVFastN pre states rd`, the frame map of the deployed decoder keyed by index
(`decode_eq_numbered`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Located
open LeanVM.Guest.Fast LeanVM.Extraction.Fast

attribute [local instance] lexOrd

@[expose] public section

theorem foldl_congr_mem {α β : Type} {f g : α → β → α} :
    ∀ (l : List β) (a : α), (∀ a, ∀ b ∈ l, f a b = g a b) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | b :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h a b List.mem_cons_self]
    exact foldl_congr_mem l _ fun a b hb ↦ h a b (List.mem_cons_of_mem _ hb)

/-- **The table of entries is the guest's.** -/
theorem pcTableT_eq : pcTableT = pcTable := by
  unfold pcTableT pcTable
  refine foldl_congr_mem _ _ fun m j hj ↦ ?_
  rw [addEntry, guestEntries_eq j (List.mem_range.mp hj)]

theorem entryKeyT_eq (rd : Reader) (r : Registers K) {j : ℕ} (hj : j < nFns) :
    entryKeyT rd r j = entryKey rd r j := by
  rw [entryKeyT, entryKey, guestArgCounts_eq j hj, guestRetCounts_eq j hj]

theorem fileStateT_eq (pre : ℕ → K → Bool) (rd : Reader) (m : SortedMap CallKey K)
    (r : Registers K) : fileStateT pcTableT pre rd m r = fileState pre rd m r := by
  rw [fileStateT, fileState, pcTableT_eq]
  refine foldl_congr_mem _ _ fun m j hj ↦ ?_
  rw [fileOne, entryKeyT_eq rd r (mem_pcTable.mp hj).1]

/-- **The entry table is the guest's.** -/
theorem entryTableT_eq (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    entryTableT pcTableT pre states rd = entryTable pre states rd := by
  have h : fileStateT pcTableT pre rd = fileState pre rd := by
    funext m r
    exact fileStateT_eq pre rd m r
  rw [entryTableT, entryTable, h]

theorem canonIndex_lt (j : ℕ) : canonIndex j < nFns := by
  unfold canonIndex isFunctionIndex nFns
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  · omega

/-- **The frame map, restated, is the deployed one** (keyed by index). -/
theorem frameAt_eq (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    frameAt (entryTableT pcTableT pre states rd) rd = frameVFastN pre states rd := by
  funext j args rets v
  rw [entryTableT_eq]
  unfold frameAt frameVFastN
  cases (entryTable pre states rd).get? (callKey (canonIndex j) args rets) with
  | none => rfl
  | some fp =>
    show wordWith rd fp ((guestLocs.getD (canonIndex j) #[]).getD v.idx 0) = _
    have h (a : Array ℕ) (i : ℕ) : a.getD i 0 = a.toList.getD i 0 := by
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    rw [h, guestLocs_eq (canonIndex_lt j)]

end

end LeanVM.Cost.Decoder
