module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_921 : kvdStaticRange 921 1 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_922 : kvdStaticRange 922 1 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
