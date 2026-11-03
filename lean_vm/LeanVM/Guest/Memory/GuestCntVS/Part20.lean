module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_860 : kvsStaticRange 860 6 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_866 : kvsStaticRange 866 8 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
