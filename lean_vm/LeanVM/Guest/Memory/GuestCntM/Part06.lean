module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_894 : kwmStaticRange 894 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_924 : kwmStaticRange 924 23 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
