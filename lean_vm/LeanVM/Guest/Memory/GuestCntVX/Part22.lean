module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_624 : kvxStaticRange 624 16 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_640 : kvxStaticRange 640 15 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
