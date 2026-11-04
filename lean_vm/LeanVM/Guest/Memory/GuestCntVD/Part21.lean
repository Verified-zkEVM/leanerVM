module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_875 : kvdStaticRange 875 7 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_882 : kvdStaticRange 882 2 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
