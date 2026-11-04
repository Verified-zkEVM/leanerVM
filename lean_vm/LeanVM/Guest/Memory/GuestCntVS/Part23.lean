module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_655 : kvsStaticRange 655 16 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_671 : kvsStaticRange 671 16 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
