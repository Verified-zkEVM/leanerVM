module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_719 : kvdStaticRange 719 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_737 : kvdStaticRange 737 18 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
