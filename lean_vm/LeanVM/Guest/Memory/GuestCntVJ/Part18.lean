module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_843 : kvjStaticRange 843 12 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_855 : kvjStaticRange 855 8 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
