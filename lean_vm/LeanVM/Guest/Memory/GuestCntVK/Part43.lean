module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_942 : kvkStaticRange 942 2 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_944 : kvkStaticRange 944 3 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
