module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_843 : kvmStaticRange 843 8 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_851 : kvmStaticRange 851 9 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
