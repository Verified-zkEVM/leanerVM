module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_933 : kvsStaticRange 933 1 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_934 : kvsStaticRange 934 1 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
