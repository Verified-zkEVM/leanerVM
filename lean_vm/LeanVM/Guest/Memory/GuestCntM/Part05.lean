module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_308 : kwmStaticRange 308 7 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_315 : kwmStaticRange 315 30 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
