module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_624 : kvmStaticRange 624 16 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_640 : kvmStaticRange 640 15 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
