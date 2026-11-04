module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_938 : kvjStaticRange 938 2 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_940 : kvjStaticRange 940 2 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
