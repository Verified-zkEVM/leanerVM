module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_816 : kvkStaticRange 816 12 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_828 : kvkStaticRange 828 11 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
