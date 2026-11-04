module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_554 : kvkStaticRange 554 18 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_572 : kvkStaticRange 572 19 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
