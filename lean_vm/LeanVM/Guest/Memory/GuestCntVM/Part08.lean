module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_308 : kvmStaticRange 308 2 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_310 : kvmStaticRange 310 1 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
