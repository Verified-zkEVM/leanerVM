module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_859 : kvjStaticRange 859 4 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_863 : kvjStaticRange 863 4 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
