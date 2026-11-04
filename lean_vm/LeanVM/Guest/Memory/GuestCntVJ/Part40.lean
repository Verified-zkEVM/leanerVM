module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_933 : kvjStaticRange 933 1 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_934 : kvjStaticRange 934 1 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
