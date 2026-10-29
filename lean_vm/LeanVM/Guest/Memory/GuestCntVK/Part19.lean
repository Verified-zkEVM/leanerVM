module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_839 : kvkStaticRange 839 7 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_846 : kvkStaticRange 846 9 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
