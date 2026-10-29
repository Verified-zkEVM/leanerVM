module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_874 : kvsStaticRange 874 6 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_880 : kvsStaticRange 880 7 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
