module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_287 : kumStaticRange 287 14 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_301 : kumStaticRange 301 7 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
