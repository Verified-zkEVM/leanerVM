module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_591 : kvmStaticRange 591 16 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_607 : kvmStaticRange 607 19 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
