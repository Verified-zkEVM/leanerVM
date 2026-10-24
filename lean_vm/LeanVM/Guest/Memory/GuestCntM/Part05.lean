module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_309 : kwmStaticRange 309 7 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_316 : kwmStaticRange 316 30 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
