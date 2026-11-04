module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_942 : kvmStaticRange 942 2 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_944 : kvmStaticRange 944 3 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
