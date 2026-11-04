module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_310 : kwmStaticRange 310 7 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_317 : kwmStaticRange 317 7 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
