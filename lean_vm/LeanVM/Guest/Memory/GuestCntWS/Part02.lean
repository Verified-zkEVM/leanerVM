module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_286 : kusStaticRange 286 13 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_299 : kusStaticRange 299 7 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
