module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_521 : kvjStaticRange 521 16 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_537 : kvjStaticRange 537 17 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
