module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_863 : kvxStaticRange 863 9 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_872 : kvxStaticRange 872 6 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
