module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_306 : kumStaticRange 306 7 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_313 : kumStaticRange 313 30 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
