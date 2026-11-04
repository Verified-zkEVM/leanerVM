module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_942 : kvdStaticRange 942 2 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_944 : kvdStaticRange 944 3 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
