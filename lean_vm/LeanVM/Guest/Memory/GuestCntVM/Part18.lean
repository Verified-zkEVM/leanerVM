module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_817 : kvmStaticRange 817 14 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_831 : kvmStaticRange 831 12 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
