module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_921 : kvjStaticRange 921 1 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_922 : kvjStaticRange 922 1 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
