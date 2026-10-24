module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_843 : kvdStaticRange 843 12 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_855 : kvdStaticRange 855 8 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
