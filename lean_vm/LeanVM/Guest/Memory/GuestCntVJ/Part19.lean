module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_863 : kvjStaticRange 863 9 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_872 : kvjStaticRange 872 6 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
