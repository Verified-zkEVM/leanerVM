module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_816 : kvxStaticRange 816 12 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_828 : kvxStaticRange 828 11 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
