module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_891 : kvdStaticRange 891 4 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_895 : kvdStaticRange 895 2 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
