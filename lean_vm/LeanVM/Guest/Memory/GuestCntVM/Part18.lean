module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_816 : kvmStaticRange 816 12 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_828 : kvmStaticRange 828 11 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
