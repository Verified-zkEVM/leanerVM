module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_291 : kwmStaticRange 291 8 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_299 : kwmStaticRange 299 7 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
