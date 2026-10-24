module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_288 : kujStaticRange 288 14 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_302 : kujStaticRange 302 7 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
