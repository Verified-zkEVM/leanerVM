module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_287 : kuxStaticRange 287 14 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_301 : kuxStaticRange 301 7 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
