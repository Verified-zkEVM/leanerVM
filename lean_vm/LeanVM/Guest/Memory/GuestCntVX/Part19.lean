module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_856 : kvxStaticRange 856 9 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_865 : kvxStaticRange 865 9 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
