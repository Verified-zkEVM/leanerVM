module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_308 : kujStaticRange 308 7 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_315 : kujStaticRange 315 30 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
