module

public import LeanVM.Cost.Decoder.GuestTables

/-!
# Bound: the guest's frame cells, functions `563` to `716`, by evaluation

One chunk of `guestLocsList_lt` (`Bounds/Decoder/GuestTablesBounds.lean`): the frame cells of
`154` functions (`19785` cells) below `2^20`, a kernel evaluation of their certificates' cells in a
module of its own (`GuestTablesFirewall.lean` checks that it imports the tables alone).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost.Decoder

public section

/-- The frame cells of functions `563` to `716` are below `2^20`. -/
theorem guestLocsChunk11_lt :
    ((guestLocsList.drop 563).take 154).all (fun l ↦ l.all (· < 2 ^ 20)) = true := by
  decide +kernel

end

end LeanVM.Cost.Bounds
