module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_306 : kwjStaticRange 306 7 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_313 : kwjStaticRange 313 30 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
