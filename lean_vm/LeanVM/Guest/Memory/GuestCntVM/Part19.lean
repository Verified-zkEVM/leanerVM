module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_856 : kvmStaticRange 856 9 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_865 : kvmStaticRange 865 9 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
