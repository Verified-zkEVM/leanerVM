module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_719 : kvkStaticRange 719 18 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_737 : kvkStaticRange 737 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
