module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_894 : kwkStaticRange 894 30 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_924 : kwkStaticRange 924 23 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
