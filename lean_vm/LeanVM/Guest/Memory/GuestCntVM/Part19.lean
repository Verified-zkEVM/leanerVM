module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_839 : kvmStaticRange 839 7 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_846 : kvmStaticRange 846 9 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
