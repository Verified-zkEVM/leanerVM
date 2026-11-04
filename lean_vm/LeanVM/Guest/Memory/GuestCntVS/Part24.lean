module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_687 : kvsStaticRange 687 14 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_701 : kvsStaticRange 701 18 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
