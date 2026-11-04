module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_290 : kuxStaticRange 290 20 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_310 : kuxStaticRange 310 7 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
