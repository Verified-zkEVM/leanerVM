module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_816 : kvjStaticRange 816 12 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_828 : kvjStaticRange 828 11 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
