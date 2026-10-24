module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdstaticRange_309 : kwdStaticRange 309 7 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_316 : kwdStaticRange 316 30 := by
  unfold kwdStaticRange; decide +kernel

end
end LeanVM.Guest
