module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_839 : kvxStaticRange 839 7 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_846 : kvxStaticRange 846 9 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
