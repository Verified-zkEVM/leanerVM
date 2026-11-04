module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_938 : kvsStaticRange 938 2 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_940 : kvsStaticRange 940 2 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
