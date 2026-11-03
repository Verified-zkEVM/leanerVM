module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_291 : kwmStaticRange 291 10 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_301 : kwmStaticRange 301 7 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
