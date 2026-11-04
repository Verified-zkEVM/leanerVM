module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_935 : kvsStaticRange 935 1 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_936 : kvsStaticRange 936 2 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
