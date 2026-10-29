module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_856 : kvjStaticRange 856 9 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_865 : kvjStaticRange 865 9 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
