module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_816 : kvdStaticRange 816 12 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_828 : kvdStaticRange 828 11 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
