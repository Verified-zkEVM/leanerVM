module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_302 : kvxStaticRange 302 2 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_304 : kvxStaticRange 304 1 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
