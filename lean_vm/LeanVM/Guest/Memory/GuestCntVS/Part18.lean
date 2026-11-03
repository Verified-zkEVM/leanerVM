module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_817 : kvsStaticRange 817 14 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_831 : kvsStaticRange 831 12 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
