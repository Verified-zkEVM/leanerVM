module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_286 : kumStaticRange 286 13 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_299 : kumStaticRange 299 7 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
