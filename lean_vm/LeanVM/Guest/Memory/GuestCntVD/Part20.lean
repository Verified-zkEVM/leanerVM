module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_554 : kvdStaticRange 554 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_572 : kvdStaticRange 572 19 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
