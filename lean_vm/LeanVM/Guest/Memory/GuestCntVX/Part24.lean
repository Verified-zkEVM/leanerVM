module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_687 : kvxStaticRange 687 14 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_701 : kvxStaticRange 701 18 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
