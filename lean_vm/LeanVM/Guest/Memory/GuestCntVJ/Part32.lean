module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_891 : kvjStaticRange 891 4 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_895 : kvjStaticRange 895 2 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
