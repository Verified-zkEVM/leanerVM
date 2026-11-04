module

public import LeanVM.Cost.Decoder.GuestTables

/-!
# Bound: the guest's frame cells, function `21`'s windows `11` to `20`, by evaluation

Function `21` (`sp_wots`, `21` windows, `32053` cells, the table's largest) evaluated by
windows (`15366` cells here), in `2` modules of their own (`GuestTablesBounds.lean`
combines them through `List.all_flatten`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost.Decoder

public section

/-- Function `21`'s frame cells, windows `11` to `20`, are below `2^20`. -/
theorem guestLocsWindows21_1_lt :
    (guestLocsRow21.drop 11).all (fun w ↦ w.all (· < 2 ^ 20)) = true := by
  decide +kernel

end

end LeanVM.Cost.Bounds
