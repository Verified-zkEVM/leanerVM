module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_687 : kvmStaticRange 687 14 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_701 : kvmStaticRange 701 18 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
