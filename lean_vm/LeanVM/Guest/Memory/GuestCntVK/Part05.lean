module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_299 : kvkStaticRange 299 2 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_301 : kvkStaticRange 301 1 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
