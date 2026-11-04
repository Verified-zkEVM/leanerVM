module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_719 : kvjStaticRange 719 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_737 : kvjStaticRange 737 18 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
