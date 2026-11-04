module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_521 : kvsStaticRange 521 16 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_537 : kvsStaticRange 537 17 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
