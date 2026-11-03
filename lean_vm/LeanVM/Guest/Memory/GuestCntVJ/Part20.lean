module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_860 : kvjStaticRange 860 6 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_866 : kvjStaticRange 866 8 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
