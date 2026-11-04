module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_655 : kvkStaticRange 655 16 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_671 : kvkStaticRange 671 16 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
