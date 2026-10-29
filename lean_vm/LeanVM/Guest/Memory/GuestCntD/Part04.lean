module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdstaticRange_291 : kwdStaticRange 291 8 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_299 : kwdStaticRange 299 7 := by
  unfold kwdStaticRange; decide +kernel

end
end LeanVM.Guest
