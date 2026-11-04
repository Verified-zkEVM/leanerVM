module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_626 : kvxStaticRange 626 16 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_642 : kvxStaticRange 642 15 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
