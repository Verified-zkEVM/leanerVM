module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_921 : kvmStaticRange 921 1 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_922 : kvmStaticRange 922 1 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
