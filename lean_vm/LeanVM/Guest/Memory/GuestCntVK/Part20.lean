module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_551 : kvkStaticRange 551 18 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_569 : kvkStaticRange 569 19 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
