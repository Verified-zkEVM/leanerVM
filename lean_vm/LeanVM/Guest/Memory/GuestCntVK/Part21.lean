module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_875 : kvkStaticRange 875 7 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_882 : kvkStaticRange 882 2 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
