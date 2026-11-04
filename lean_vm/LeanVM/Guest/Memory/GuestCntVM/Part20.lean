module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_861 : kvmStaticRange 861 6 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_867 : kvmStaticRange 867 8 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
