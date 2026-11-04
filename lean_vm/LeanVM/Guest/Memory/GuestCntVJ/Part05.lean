module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_302 : kvjStaticRange 302 2 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_304 : kvjStaticRange 304 1 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
