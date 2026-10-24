module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_309 : kvdStaticRange 309 2 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_311 : kvdStaticRange 311 1 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
