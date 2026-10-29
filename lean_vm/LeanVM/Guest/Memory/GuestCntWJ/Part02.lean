module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_286 : kujStaticRange 286 13 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_299 : kujStaticRange 299 7 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
