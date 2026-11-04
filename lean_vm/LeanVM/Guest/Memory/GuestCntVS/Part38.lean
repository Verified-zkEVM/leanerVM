module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_923 : kvsStaticRange 923 2 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_925 : kvsStaticRange 925 2 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
