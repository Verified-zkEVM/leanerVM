module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_290 : kujStaticRange 290 20 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_310 : kujStaticRange 310 7 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
