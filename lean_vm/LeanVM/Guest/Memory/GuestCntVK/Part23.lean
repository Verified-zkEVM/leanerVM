module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_657 : kvkStaticRange 657 16 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_673 : kvkStaticRange 673 15 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
