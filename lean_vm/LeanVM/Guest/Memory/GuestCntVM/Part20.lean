module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_554 : kvmStaticRange 554 18 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_572 : kvmStaticRange 572 19 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
