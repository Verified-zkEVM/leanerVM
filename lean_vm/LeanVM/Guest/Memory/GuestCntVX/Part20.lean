module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_860 : kvxStaticRange 860 6 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_866 : kvxStaticRange 866 8 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
