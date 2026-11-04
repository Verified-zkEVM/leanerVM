module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_938 : kvxStaticRange 938 2 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_940 : kvxStaticRange 940 2 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
