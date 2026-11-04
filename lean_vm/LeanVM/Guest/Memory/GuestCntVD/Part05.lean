module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_302 : kvdStaticRange 302 2 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_304 : kvdStaticRange 304 1 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
