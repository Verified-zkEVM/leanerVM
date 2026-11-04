module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_942 : kvjStaticRange 942 2 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_944 : kvjStaticRange 944 3 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
