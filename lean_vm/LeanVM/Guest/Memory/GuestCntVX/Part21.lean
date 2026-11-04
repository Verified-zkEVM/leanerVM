module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_588 : kvxStaticRange 588 17 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_605 : kvxStaticRange 605 19 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
