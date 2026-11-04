module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_721 : kvjStaticRange 721 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_739 : kvjStaticRange 739 19 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
