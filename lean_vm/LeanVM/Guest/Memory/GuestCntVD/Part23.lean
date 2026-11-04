module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_655 : kvdStaticRange 655 16 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_671 : kvdStaticRange 671 16 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
