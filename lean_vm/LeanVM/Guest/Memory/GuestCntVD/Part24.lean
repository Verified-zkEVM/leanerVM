module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_688 : kvdStaticRange 688 16 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_704 : kvdStaticRange 704 17 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
