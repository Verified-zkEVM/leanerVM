module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_302 : kvsStaticRange 302 2 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_304 : kvsStaticRange 304 1 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
