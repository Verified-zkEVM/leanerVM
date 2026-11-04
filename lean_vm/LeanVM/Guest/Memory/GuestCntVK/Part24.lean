module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_687 : kvkStaticRange 687 14 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_701 : kvkStaticRange 701 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
