module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_655 : kvxStaticRange 655 16 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_671 : kvxStaticRange 671 16 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
