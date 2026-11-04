module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_875 : kvmStaticRange 875 7 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_882 : kvmStaticRange 882 2 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
