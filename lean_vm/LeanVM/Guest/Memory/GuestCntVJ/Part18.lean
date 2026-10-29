module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_831 : kvjStaticRange 831 13 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_844 : kvjStaticRange 844 12 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
