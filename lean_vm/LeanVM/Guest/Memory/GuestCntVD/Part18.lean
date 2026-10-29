module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_831 : kvdStaticRange 831 13 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_844 : kvdStaticRange 844 12 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
