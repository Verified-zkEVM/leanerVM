module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_302 : kvmStaticRange 302 2 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_304 : kvmStaticRange 304 1 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
