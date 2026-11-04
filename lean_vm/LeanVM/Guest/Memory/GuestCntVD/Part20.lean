module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_551 : kvdStaticRange 551 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_569 : kvdStaticRange 569 19 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
