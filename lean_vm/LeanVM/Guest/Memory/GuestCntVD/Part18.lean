module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_817 : kvdStaticRange 817 14 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_831 : kvdStaticRange 831 12 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
