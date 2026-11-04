module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_309 : kvjStaticRange 309 2 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_311 : kvjStaticRange 311 1 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
