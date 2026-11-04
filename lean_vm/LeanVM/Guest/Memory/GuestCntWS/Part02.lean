module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_290 : kusStaticRange 290 20 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_310 : kusStaticRange 310 7 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
