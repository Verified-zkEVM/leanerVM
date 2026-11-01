module

public import LeanVM.Cost.Decoder.GuestTables

/-!
# Bound: the guest's tables, their largest entries, by evaluation

A module of its own, importing the tables alone (`Cost/Decoder/GuestTables.lean`, literals of
the decoder program): the largest entry pc (below `2^19`), argument count (`22`), return count
(`10`), frame cell (below `2^20`), and how often an entry pc repeats (at most twice). The entry
table's bounds (`Bounds/Decoder/EntryTable.lean`) read these.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost.Decoder

public section

/-- Every entry pc is below `2^19`. -/
theorem guestEntriesList_lt : guestEntriesList.all (· < 2 ^ 19) = true := by decide +kernel

/-- Every argument count is at most `22`. -/
theorem guestArgCountsList_le : guestArgCountsList.all (· ≤ 22) = true := by decide +kernel

/-- Every return count is at most `10`. -/
theorem guestRetCountsList_le : guestRetCountsList.all (· ≤ 10) = true := by decide +kernel

/-- Every frame cell is below `2^20`. -/
theorem guestLocsList_lt : guestLocsList.all (fun l ↦ l.all (· < 2 ^ 20)) = true := by
  decide +kernel

/-- An entry pc is the entry of at most two functions. -/
theorem guestEntriesList_count : guestEntriesList.all (fun e ↦ guestEntriesList.count e ≤ 2) =
    true := by
  decide +kernel

end

end LeanVM.Cost.Bounds
