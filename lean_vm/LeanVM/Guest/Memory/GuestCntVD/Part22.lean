module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_624 : kvdStaticRange 624 16 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_640 : kvdStaticRange 640 15 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
