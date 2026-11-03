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
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk14
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk15
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Chunk16
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Windows21_0
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Windows21_1
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Windows21_2
public import LeanVM.Cost.Bounds.Decoder.GuestLocs.Windows21_3

/-!
# Bound: the guest's tables, their largest entries, by evaluation

The largest entry pc (below `2^19`), argument count (`22`), return count (`10`) and frame cell
(below `2^20`) of the guest's tables (`Cost/Decoder/GuestTables.lean`, literals of the decoder
program), and how often an entry pc repeats (never: they increase, a linear check). The entry
table's bounds (`Bounds/Decoder/EntryTable.lean`) read these.

The frame cells read every certificate: the whole table at once peaks over `12 GB` in the kernel.
So they are evaluated in `17` chunks of functions of at most `25039` cells, and function `21`
(`69213` cells) in `4` chunks of its windows, each a module of its own below `2 GB`
(`GuestLocs/*.lean`), combined here (`all_of_drop`, `guestLocs21`); `GuestTablesFirewall.lean`
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
theorem guestLocs21 : (guestLocsList.drop 21).take 1 = [([Data.cert21_w0_0, Data.cert21_w1_0, Data.cert21_w2_0, Data.cert21_w3_0, Data.cert21_w4_0, Data.cert21_w5_0, Data.cert21_w6_0, Data.cert21_w7_0, Data.cert21_w8_0, Data.cert21_w9_0, Data.cert21_w10_0, Data.cert21_w11_0, Data.cert21_w12_0, Data.cert21_w13_0, Data.cert21_w14_0, Data.cert21_w15_0, Data.cert21_w16_0, Data.cert21_w17_0, Data.cert21_w18_0, Data.cert21_w19_0, Data.cert21_w20_0, Data.cert21_w21_0, Data.cert21_w22_0, Data.cert21_w23_0] ++ [Data.cert21_w24_0, Data.cert21_w25_0, Data.cert21_w26_0, Data.cert21_w27_0, Data.cert21_w28_0, Data.cert21_w29_0, Data.cert21_w30_0, Data.cert21_w31_0, Data.cert21_w32_0, Data.cert21_w33_0, Data.cert21_w34_0, Data.cert21_w35_0, Data.cert21_w36_0, Data.cert21_w37_0, Data.cert21_w38_0, Data.cert21_w39_0, Data.cert21_w40_0, Data.cert21_w41_0, Data.cert21_w42_0, Data.cert21_w43_0, Data.cert21_w44_0, Data.cert21_w45_0, Data.cert21_w46_0, Data.cert21_w47_0] ++ [Data.cert21_w48_0, Data.cert21_w49_0, Data.cert21_w50_0, Data.cert21_w51_0, Data.cert21_w52_0, Data.cert21_w53_0, Data.cert21_w54_0, Data.cert21_w55_0, Data.cert21_w56_0, Data.cert21_w57_0, Data.cert21_w58_0, Data.cert21_w59_0, Data.cert21_w60_0, Data.cert21_w61_0, Data.cert21_w62_0, Data.cert21_w63_0, Data.cert21_w64_0, Data.cert21_w65_0, Data.cert21_w66_0, Data.cert21_w67_0, Data.cert21_w68_0, Data.cert21_w69_0, Data.cert21_w70_0, Data.cert21_w71_0] ++ [Data.cert21_w72_0, Data.cert21_w73_0, Data.cert21_w74_0, Data.cert21_w75_0, Data.cert21_w76_0, Data.cert21_w77_0, Data.cert21_w78_0, Data.cert21_w79_0, Data.cert21_w80_0, Data.cert21_w81_0, Data.cert21_w82_0, Data.cert21_w83_0, Data.cert21_w84_0, Data.cert21_w85_0, Data.cert21_w86_0, Data.cert21_w87_0, Data.cert21_w88_0, Data.cert21_w89_0, Data.cert21_w90_0, Data.cert21_w91_0, Data.cert21_w92_0]).flatten] := rfl

/-- Function `21`'s frame cells are below `2^20`: its `4` chunks of windows. -/
theorem guestLocs21_lt :
    ((guestLocsList.drop 21).take 1).all (fun l ↦ l.all (· < 2 ^ 20)) = true := by
  rw [guestLocs21, List.all_cons, List.all_nil, Bool.and_true, List.all_flatten, List.all_append,
    List.all_append, List.all_append, guestLocsWindows21_0_lt, guestLocsWindows21_1_lt,
    guestLocsWindows21_2_lt, guestLocsWindows21_3_lt]
  rfl

set_option maxRecDepth 100000 in
/-- The table of frame cells ends after `884` functions. -/
theorem guestLocsList_drop_end : guestLocsList.drop 884 = [] := rfl

/-- Every frame cell is below `2^20`: the chunks' evaluations combined. -/
theorem guestLocsList_lt : guestLocsList.all (fun l ↦ l.all (· < 2 ^ 20)) = true := by
  rw [← List.drop_zero (l := guestLocsList)]
  refine all_of_drop _ _ 0 16 guestLocsChunk0_lt ?_
  refine all_of_drop _ _ 16 4 guestLocsChunk1_lt ?_
  refine all_of_drop _ _ 20 1 guestLocsChunk2_lt ?_
  refine all_of_drop _ _ 21 1 guestLocs21_lt ?_
  refine all_of_drop _ _ 22 146 guestLocsChunk3_lt ?_
  refine all_of_drop _ _ 168 88 guestLocsChunk4_lt ?_
  refine all_of_drop _ _ 256 43 guestLocsChunk5_lt ?_
  refine all_of_drop _ _ 299 8 guestLocsChunk6_lt ?_
  refine all_of_drop _ _ 307 8 guestLocsChunk7_lt ?_
  refine all_of_drop _ _ 315 17 guestLocsChunk8_lt ?_
  refine all_of_drop _ _ 332 87 guestLocsChunk9_lt ?_
  refine all_of_drop _ _ 419 144 guestLocsChunk10_lt ?_
  refine all_of_drop _ _ 563 154 guestLocsChunk11_lt ?_
  refine all_of_drop _ _ 717 113 guestLocsChunk12_lt ?_
  refine all_of_drop _ _ 830 20 guestLocsChunk13_lt ?_
  refine all_of_drop _ _ 850 16 guestLocsChunk14_lt ?_
  refine all_of_drop _ _ 866 14 guestLocsChunk15_lt ?_
  refine all_of_drop _ _ 880 4 guestLocsChunk16_lt ?_
  show (guestLocsList.drop 884).all _ = true
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
