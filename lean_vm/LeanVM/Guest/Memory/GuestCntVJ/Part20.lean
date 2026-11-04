module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_551 : kvjStaticRange 551 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_569 : kvjStaticRange 569 19 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
