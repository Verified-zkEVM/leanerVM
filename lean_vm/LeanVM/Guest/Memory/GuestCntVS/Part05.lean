module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_299 : kvsStaticRange 299 2 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_301 : kvsStaticRange 301 1 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
