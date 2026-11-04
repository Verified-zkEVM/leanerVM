module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_518 : kvsStaticRange 518 16 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_534 : kvsStaticRange 534 17 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
