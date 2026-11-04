module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_935 : kvkStaticRange 935 1 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_936 : kvkStaticRange 936 2 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
