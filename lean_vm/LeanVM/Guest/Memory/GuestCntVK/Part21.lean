module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_591 : kvkStaticRange 591 16 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_607 : kvkStaticRange 607 19 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
