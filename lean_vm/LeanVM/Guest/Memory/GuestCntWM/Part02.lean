module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_288 : kumStaticRange 288 14 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_302 : kumStaticRange 302 7 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
