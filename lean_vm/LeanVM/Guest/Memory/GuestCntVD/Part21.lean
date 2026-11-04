module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_588 : kvdStaticRange 588 17 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_605 : kvdStaticRange 605 19 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
