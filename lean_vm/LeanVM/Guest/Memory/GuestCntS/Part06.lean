module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_894 : kwsStaticRange 894 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_924 : kwsStaticRange 924 23 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
