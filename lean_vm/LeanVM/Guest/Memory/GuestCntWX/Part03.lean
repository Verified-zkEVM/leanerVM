module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_306 : kuxStaticRange 306 7 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_313 : kuxStaticRange 313 30 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
