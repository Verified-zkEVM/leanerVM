module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_309 : kvxStaticRange 309 2 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_311 : kvxStaticRange 311 1 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
