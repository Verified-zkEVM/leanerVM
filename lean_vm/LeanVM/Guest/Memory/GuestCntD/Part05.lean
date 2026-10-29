module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdstaticRange_306 : kwdStaticRange 306 7 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_313 : kwdStaticRange 313 30 := by
  unfold kwdStaticRange; decide +kernel

end
end LeanVM.Guest
