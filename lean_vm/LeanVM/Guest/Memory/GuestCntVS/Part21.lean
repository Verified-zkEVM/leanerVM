module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_875 : kvsStaticRange 875 7 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_882 : kvsStaticRange 882 2 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
