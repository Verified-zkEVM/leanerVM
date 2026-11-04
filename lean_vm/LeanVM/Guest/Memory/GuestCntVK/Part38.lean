module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_923 : kvkStaticRange 923 2 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_925 : kvkStaticRange 925 2 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
