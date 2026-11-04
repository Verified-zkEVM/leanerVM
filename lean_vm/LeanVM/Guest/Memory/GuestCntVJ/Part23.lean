module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_655 : kvjStaticRange 655 16 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_671 : kvjStaticRange 671 16 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
