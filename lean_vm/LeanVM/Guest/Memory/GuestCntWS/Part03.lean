module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_308 : kusStaticRange 308 7 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_315 : kusStaticRange 315 30 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
