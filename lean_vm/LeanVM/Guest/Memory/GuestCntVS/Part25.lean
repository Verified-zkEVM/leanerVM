module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_719 : kvsStaticRange 719 18 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_737 : kvsStaticRange 737 18 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
