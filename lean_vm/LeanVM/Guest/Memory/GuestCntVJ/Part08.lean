module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_308 : kvjStaticRange 308 2 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_310 : kvjStaticRange 310 1 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
