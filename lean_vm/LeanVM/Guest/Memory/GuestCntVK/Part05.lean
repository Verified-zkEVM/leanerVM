module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_302 : kvkStaticRange 302 2 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_304 : kvkStaticRange 304 1 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
