module

public import LeanVM.Cost.Decoder.GuestTables
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk0
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk1
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk2
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk3
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk4
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk5
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk6
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk7
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk8
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk9
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk10
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk11
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk12
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk13
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Windows21_0
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Windows21_1

/-!
# Bound: the guest's tables, their largest entries, by evaluation

The largest entry pc (below `2^19`), argument count (`22`), return count (`10`) and frame cell
(below `2^20`) of the guest's tables (`Cost/Decoder/GuestTables.lean`, literals of the decoder
program), and how often an entry pc repeats (never: they increase, a linear check). The entry
table's bounds (`Bounds/Decoder/EntryTable.lean`) read these.

The frame cells read every certificate: the whole table at once peaks over `12 GB` in the kernel.
So they are evaluated in `14` chunks of functions of at most `25039` cells, and function `21`
(`sp_wots`, `32053` cells, `guestLocsRow21`) in `2` chunks of its windows, each a module of its
own below `2 GB` (`GuestLocs/*.lean`), combined here (`all_of_drop`, `guestLocs21`); `GuestTablesFirewall.lean`
checks that the chunks import the tables alone.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost.Decoder LeanVM.Guest

public section

/-- Every entry pc is below `2^19`. -/
theorem guestEntriesList_lt : guestEntriesList.all (· < 2 ^ 19) = true := by decide +kernel

/-- Every argument count is at most `22`. -/
theorem guestArgCountsList_le : guestArgCountsList.all (· ≤ 22) = true := by decide +kernel

/-- Every return count is at most `10`. -/
theorem guestRetCountsList_le : guestRetCountsList.all (· ≤ 10) = true := by decide +kernel

/-- A list holds a test from `a` on if it holds the `n` entries from `a` and the rest. -/
theorem all_of_drop {α : Type} (p : α → Bool) (l : List α) (a n : ℕ)
    (h1 : ((l.drop a).take n).all p = true) (h2 : (l.drop (a + n)).all p = true) :
    (l.drop a).all p = true := by
  rw [← List.take_append_drop n (l.drop a), List.all_append, Bool.and_eq_true, List.drop_drop]
  exact ⟨h1, h2⟩

set_option maxRecDepth 100000 in
/-- Function `21`'s frame cells, by its windows. -/
theorem guestLocs21 : (guestLocsList.drop 21).take 1 = [guestLocsRow21.flatten] := rfl

/-- Function `21`'s frame cells are below `2^20`: its `2` chunks of windows. -/
theorem guestLocs21_lt :
    ((guestLocsList.drop 21).take 1).all (fun l ↦ l.all (· < 2 ^ 20)) = true := by
  rw [guestLocs21, List.all_cons, List.all_nil, Bool.and_true, List.all_flatten,
    ← List.take_append_drop 11 guestLocsRow21, List.all_append, guestLocsWindows21_0_lt,
    guestLocsWindows21_1_lt]
  rfl

set_option maxRecDepth 100000 in
/-- The table of frame cells ends after `885` functions. -/
theorem guestLocsList_drop_end : guestLocsList.drop 885 = [] := rfl

/-- Every frame cell is below `2^20`: the chunks' evaluations combined. -/
theorem guestLocsList_lt : guestLocsList.all (fun l ↦ l.all (· < 2 ^ 20)) = true := by
  rw [← List.drop_zero (l := guestLocsList)]
  refine all_of_drop _ _ 0 16 guestLocsChunk0_lt ?_
  refine all_of_drop _ _ 16 4 guestLocsChunk1_lt ?_
  refine all_of_drop _ _ 20 1 guestLocsChunk2_lt ?_
  refine all_of_drop _ _ 21 1 guestLocs21_lt ?_
  refine all_of_drop _ _ 22 157 guestLocsChunk3_lt ?_
  refine all_of_drop _ _ 179 107 guestLocsChunk4_lt ?_
  refine all_of_drop _ _ 286 20 guestLocsChunk5_lt ?_
  refine all_of_drop _ _ 306 10 guestLocsChunk6_lt ?_
  refine all_of_drop _ _ 316 40 guestLocsChunk7_lt ?_
  refine all_of_drop _ _ 356 112 guestLocsChunk8_lt ?_
  refine all_of_drop _ _ 468 178 guestLocsChunk9_lt ?_
  refine all_of_drop _ _ 646 180 guestLocsChunk10_lt ?_
  refine all_of_drop _ _ 826 25 guestLocsChunk11_lt ?_
  refine all_of_drop _ _ 851 19 guestLocsChunk12_lt ?_
  refine all_of_drop _ _ 870 15 guestLocsChunk13_lt ?_
  show (guestLocsList.drop 885).all _ = true
  rw [guestLocsList_drop_end]
  rfl

/-- The entry pcs increase, a linear check (the quadratic count of each peaked over `12 GB`). -/
theorem guestEntriesList_chain : guestEntriesList.IsChain (· < ·) := by decide +kernel

/-- An entry pc is the entry of at most two functions (of one: they increase). -/
theorem guestEntriesList_count : guestEntriesList.all (fun e ↦ guestEntriesList.count e ≤ 2) =
    true := by
  have hp : guestEntriesList.Pairwise (· < ·) :=
    List.isChain_iff_pairwise.mp guestEntriesList_chain
  have hn : guestEntriesList.Nodup := hp.imp Nat.ne_of_lt
  rw [List.all_eq_true]
  intro e _
  have := List.nodup_iff_count_le_one.mp hn e
  exact decide_eq_true (by omega)

end

end LeanVM.Cost.Bounds
