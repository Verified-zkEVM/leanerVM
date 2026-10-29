module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_291 : kwkStaticRange 291 8 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_299 : kwkStaticRange 299 7 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
