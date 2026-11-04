module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_624 : kvsStaticRange 624 16 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_640 : kvsStaticRange 640 15 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
