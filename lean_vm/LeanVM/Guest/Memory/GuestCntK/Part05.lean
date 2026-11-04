module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_308 : kwkStaticRange 308 7 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_315 : kwkStaticRange 315 30 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
