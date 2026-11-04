module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_657 : kvjStaticRange 657 16 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_673 : kvjStaticRange 673 15 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
