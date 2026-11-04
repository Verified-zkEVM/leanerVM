module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_624 : kvjStaticRange 624 16 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_640 : kvjStaticRange 640 15 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
