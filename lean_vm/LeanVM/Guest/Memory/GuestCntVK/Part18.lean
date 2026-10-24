module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_843 : kvkStaticRange 843 12 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_855 : kvkStaticRange 855 8 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
