module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_861 : kvkStaticRange 861 6 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_867 : kvkStaticRange 867 8 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
