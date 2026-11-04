module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_885 : kvsStaticRange 885 2 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_887 : kvsStaticRange 887 4 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
