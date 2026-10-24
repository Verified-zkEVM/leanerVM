module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_863 : kvmStaticRange 863 9 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_872 : kvmStaticRange 872 6 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
