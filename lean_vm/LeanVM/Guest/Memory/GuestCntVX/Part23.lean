module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_657 : kvxStaticRange 657 16 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_673 : kvxStaticRange 673 15 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
