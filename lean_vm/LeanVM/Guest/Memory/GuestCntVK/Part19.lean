module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_844 : kvkStaticRange 844 8 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_852 : kvkStaticRange 852 9 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
