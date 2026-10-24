module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_291 : kwkStaticRange 291 11 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_302 : kwkStaticRange 302 7 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
