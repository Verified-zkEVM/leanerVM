module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_856 : kvsStaticRange 856 9 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_865 : kvsStaticRange 865 9 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
