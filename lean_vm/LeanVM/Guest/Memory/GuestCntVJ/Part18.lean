module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_818 : kvjStaticRange 818 14 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_832 : kvjStaticRange 832 12 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
