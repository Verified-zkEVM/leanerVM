module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_624 : kvkStaticRange 624 16 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_640 : kvkStaticRange 640 15 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
