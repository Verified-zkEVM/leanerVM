module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_856 : kvdStaticRange 856 9 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_865 : kvdStaticRange 865 9 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
