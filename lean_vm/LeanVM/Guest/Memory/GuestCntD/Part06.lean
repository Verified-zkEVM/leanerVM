module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdstaticRange_894 : kwdStaticRange 894 30 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_924 : kwdStaticRange 924 23 := by
  unfold kwdStaticRange; decide +kernel

end
end LeanVM.Guest
