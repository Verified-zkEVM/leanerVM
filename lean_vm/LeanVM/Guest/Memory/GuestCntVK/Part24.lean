module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_688 : kvkStaticRange 688 16 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_704 : kvkStaticRange 704 17 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
