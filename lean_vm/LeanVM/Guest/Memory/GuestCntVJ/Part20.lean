module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_874 : kvjStaticRange 874 6 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_880 : kvjStaticRange 880 7 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
