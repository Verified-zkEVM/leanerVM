module

public import LeanVM.Cost.Decoder.GuestTables

/-!
# Bound: the guest's frame cells, functions `0` to `15`, by evaluation

One chunk of `guestLocsList_lt` (`Bounds/Decoder/GuestTablesBounds.lean`): the frame cells of
16 functions (`19701` cells) below `2^20`, a kernel evaluation of their certificates' cells in a
module of its own (`GuestTablesFirewall.lean` checks that it imports the tables alone).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost.Decoder

public section

/-- The frame cells of functions `0` to `15` are below `2^20`. -/
theorem guestLocsChunk0_lt :
    ((guestLocsList.drop 0).take 16).all (fun l ↦ l.all (· < 2 ^ 20)) = true := by
  decide +kernel

end

end LeanVM.Cost.Bounds
