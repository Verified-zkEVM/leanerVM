module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_588 : kvjStaticRange 588 17 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_605 : kvjStaticRange 605 19 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
