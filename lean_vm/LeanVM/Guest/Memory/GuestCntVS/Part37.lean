module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_921 : kvsStaticRange 921 1 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_922 : kvsStaticRange 922 1 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
