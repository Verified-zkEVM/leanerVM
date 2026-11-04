module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_860 : kvkStaticRange 860 6 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_866 : kvkStaticRange 866 8 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
