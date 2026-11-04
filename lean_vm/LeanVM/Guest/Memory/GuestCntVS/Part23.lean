module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_657 : kvsStaticRange 657 16 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_673 : kvsStaticRange 673 15 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
