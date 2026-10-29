module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_286 : kuxStaticRange 286 13 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_299 : kuxStaticRange 299 7 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
