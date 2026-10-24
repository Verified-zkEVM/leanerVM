module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_291 : kwjStaticRange 291 11 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_302 : kwjStaticRange 302 7 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
