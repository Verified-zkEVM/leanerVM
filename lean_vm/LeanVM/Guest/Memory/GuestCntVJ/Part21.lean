module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_591 : kvjStaticRange 591 16 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_607 : kvjStaticRange 607 19 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
