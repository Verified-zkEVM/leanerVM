module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_844 : kvmStaticRange 844 8 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_852 : kvmStaticRange 852 9 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
