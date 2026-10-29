module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_874 : kvkStaticRange 874 6 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_880 : kvkStaticRange 880 7 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
