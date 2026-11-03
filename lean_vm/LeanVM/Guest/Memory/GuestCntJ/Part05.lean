module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_308 : kwjStaticRange 308 7 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_315 : kwjStaticRange 315 30 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
