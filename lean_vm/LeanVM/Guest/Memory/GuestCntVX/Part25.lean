module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_719 : kvxStaticRange 719 18 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_737 : kvxStaticRange 737 18 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
