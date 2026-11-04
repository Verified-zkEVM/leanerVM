module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_719 : kvmStaticRange 719 18 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_737 : kvmStaticRange 737 18 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
