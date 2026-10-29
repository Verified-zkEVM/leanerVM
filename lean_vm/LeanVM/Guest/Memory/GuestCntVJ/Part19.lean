module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_839 : kvjStaticRange 839 7 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_846 : kvjStaticRange 846 9 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
