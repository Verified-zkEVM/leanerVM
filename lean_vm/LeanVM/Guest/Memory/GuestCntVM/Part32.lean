module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_891 : kvmStaticRange 891 4 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_895 : kvmStaticRange 895 2 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
