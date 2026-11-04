module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_308 : kumStaticRange 308 7 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_315 : kumStaticRange 315 30 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
