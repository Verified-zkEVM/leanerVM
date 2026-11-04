module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_591 : kvsStaticRange 591 16 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_607 : kvsStaticRange 607 19 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
