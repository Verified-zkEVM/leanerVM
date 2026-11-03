module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_287 : kujStaticRange 287 14 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_301 : kujStaticRange 301 7 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
