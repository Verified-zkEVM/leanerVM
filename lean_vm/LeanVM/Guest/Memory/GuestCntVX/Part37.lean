module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_921 : kvxStaticRange 921 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_922 : kvxStaticRange 922 1 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
