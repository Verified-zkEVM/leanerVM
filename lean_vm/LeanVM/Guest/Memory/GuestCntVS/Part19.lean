module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_839 : kvsStaticRange 839 7 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_846 : kvsStaticRange 846 9 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
