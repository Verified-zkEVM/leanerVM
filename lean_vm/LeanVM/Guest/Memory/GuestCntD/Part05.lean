module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdstaticRange_308 : kwdStaticRange 308 7 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_315 : kwdStaticRange 315 30 := by
  unfold kwdStaticRange; decide +kernel

end
end LeanVM.Guest
