module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_308 : kvkStaticRange 308 2 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_310 : kvkStaticRange 310 1 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
