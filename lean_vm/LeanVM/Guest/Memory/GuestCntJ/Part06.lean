module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_894 : kwjStaticRange 894 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_924 : kwjStaticRange 924 23 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
