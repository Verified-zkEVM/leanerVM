module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_591 : kvxStaticRange 591 16 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_607 : kvxStaticRange 607 19 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
