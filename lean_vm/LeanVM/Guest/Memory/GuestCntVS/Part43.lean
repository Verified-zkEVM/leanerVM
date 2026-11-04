module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_942 : kvsStaticRange 942 2 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_944 : kvsStaticRange 944 3 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
