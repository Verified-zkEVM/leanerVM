module

public import LeanVM.Cost.Decoder.GuestTables

/-!
# Bound: the guest's frame cells, functions `870` to `884`, by evaluation

One chunk of `guestLocsList_lt` (`Bounds/Decoder/GuestTablesBounds.lean`): the frame cells of
15 functions (`19187` cells) below `2^20`, a kernel evaluation of their certificates' cells in a
module of its own (`GuestTablesFirewall.lean` checks that it imports the tables alone).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost.Decoder

public section

/-- The frame cells of functions `870` to `884` are below `2^20`. -/
theorem guestLocsChunk13_lt :
    ((guestLocsList.drop 870).take 15).all (fun l ↦ l.all (· < 2 ^ 20)) = true := by
  decide +kernel

end

end LeanVM.Cost.Bounds
