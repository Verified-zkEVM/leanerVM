module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_874 : kvmStaticRange 874 6 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_880 : kvmStaticRange 880 7 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
