module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_921 : kvkStaticRange 921 1 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_922 : kvkStaticRange 922 1 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
