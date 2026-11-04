module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_721 : kvmStaticRange 721 18 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_739 : kvmStaticRange 739 19 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
